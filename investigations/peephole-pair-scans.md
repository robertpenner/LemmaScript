# Do statement-pair scans need repeated passes?

Investigation for [robertpenner/LemmaScript#8](https://github.com/robertpenner/LemmaScript/issues/8).

## Recommendation

The owner should decide whether to adopt a bounded normalization change for
the supported bare-block and switch fall-through cases below. Both produce
different output on a second invocation on both backend transforms. Repeated
scanning reaches that second output, and a third invocation makes no change.
The original 34-function corpus still has no differences.

The observed defect is incomplete simplification: the earlier map lookup
retains a temporary option and match after one invocation. Both source
reproducers verify with the current Dafny backend. This is not a demonstrated
semantic-preservation failure. Production statement scanning remains unchanged;
issue #8 does not authorize an algorithm change.

## Revisions and rule

The experiment reads the optimizer from fork `main` at `36eb31d`, independently
of the constructor/map traversal fix in #9. The reference branch is upstream
`e6e2293`: its
[`rewriteStmtListPairs` / `pairScanToFix`](https://github.com/midspiral/LemmaScript/blob/e6e2293/tools/src/peephole.ts)
rescans while a pass shortens the list. Its
[design note, section 8.6](https://github.com/midspiral/LemmaScript/blob/e6e2293/DESIGN_LS_IN_LS.md#86-porting-doctrine-extend-the-toolchain-dont-contort-the-source)
attributes repeated scanning to normalization findings.

The current [`peepholeModule`](../tools/src/peephole.ts) first optimizes each
statement and its children, then scans left to right. Its only pair rule is:

```text
immutable let x = m.get(k);
match x { Some(v): someBody; None: noneBody }

becomes

if m.has(k) { immutable let v = m[k]; someBody } else { noneBody }
```

The optional `v` binding is omitted for a wildcard. The rule declines mutable
bindings, a wrong scrutinee, non-map/non-get calls, malformed Some/None arms,
or an occurrence of `x` in the later statement suffix. That last check reads
the suffix before later pairs have merged.

The merged outer statement is an `if`, so it cannot itself become the `let`
or `match` required for a newly adjacent pair at that list level. The remaining
candidate is a later merge removing the last suffix reference that previously
blocked an earlier pair.

## Concrete synthetic difference

Use two adjacent pairs that both bind the name `x`:

```text
let x = m.get("a"); match x { Some(_): []; None: [] }
let x = m.get("b"); match x { Some(_): []; None: [] }
```

The first invocation leaves the first pair and merges the second, producing
three statements. The second invocation merges the first, producing two.
Repeated scanning reaches the same two-statement output on both backends.
With the second binder renamed to `y`, one invocation already merges both.

For the first pair, the suffix use that disappears is the second match's
scrutinee `x`. The later merge retains the map receiver, key, and both arm
bodies, while eliminating its temporary option variable's scrutinee reference.
Consequently this mechanism needs the later temporary to have the same textual
name as the earlier one. This describes this pair rule; it is not a formal
idempotence theorem for the whole optimizer.

### Supported-source differences

Separate bare blocks can legally declare the same `const` name. The extractor
flattens their statements into one list without renaming the declarations:

```ts
export function blocks(m: Map<string, number>): number {
  let total = 0;
  {
    const x = m.get("a");
    if (x !== undefined) {
      total += x;
    } else {
      total += 0;
    }
  }
  {
    const x = m.get("b");
    if (x !== undefined) {
      total += x;
    } else {
      total += 0;
    }
  }
  return total;
}
```

The following readable rendering shows the complete generated method body at
each stage. `let` is immutable; `mutable let` records the IR's mutable flag.
The affected statement IR is identical on the Dafny and Lean transforms.
These are IR renderings, not backend source syntax.

Input, before the optimizer:

```text
mutable let total: int = 0
let x: optional<int> = m.get("a")
match x {
  some(_x_val): total := total + _x_val
  none: total := total + 0
}
let x: optional<int> = m.get("b")
match x {
  some(_x_val): total := total + _x_val
  none: total := total + 0
}
return total
```

First complete optimizer invocation:

```text
mutable let total: int = 0
let x: optional<int> = m.get("a")
match x {
  some(_x_val): total := total + _x_val
  none: total := total + 0
}
if m.has("b") {
  let _x_val: int = m["b"]
  total := total + _x_val
} else {
  total := total + 0
}
return total
```

Second complete invocation, also the repeated-scan result:

```text
mutable let total: int = 0
if m.has("a") {
  let _x_val: int = m["a"]
  total := total + _x_val
} else {
  total := total + 0
}
if m.has("b") {
  let _x_val: int = m["b"]
  total := total + _x_val
} else {
  total := total + 0
}
return total
```

Braced switch cases also flatten, and fall-through concatenates successive
case bodies. The experiment's `fallthrough` function puts the `"a"` lookup in
`case "a"` and the `"b"` lookup in `case "b"`, with a `break` after the second
lookup. Its first match arm therefore has the same four input statements,
three first-output statements, and two second-output statements shown above,
excluding the enclosing `total` initialization and return. The second arm
contains only the `"b"` lookup, which merges on the first invocation. An
explicit default arm adds zero to `total` and breaks. This ensures exhaustive
generated Dafny matching; the version without a default is rejected by Dafny.
The complete source is in the executable experiment.

Both positive sources pass strict TypeScript diagnostics and production Dafny
verification (one verified, zero errors each). Lean evidence here covers its
transformed IR, not verification of the generated Lean reproducer. These
results establish the map-get shapes above; they do not establish that arbitrary
flattened duplicate declarations are accepted by either backend.

Source shadowing inside an `if` remains a negative control: child lists are
optimized before the enclosing suffix check. Bare-block flattening and switch
fall-through therefore require separate coverage.

## Reproducible experiment

From the repository root, with the compiler development dependencies installed:

```sh
node --import tsx investigations/peephole-pair-scans.ts
node node_modules/typescript/bin/tsc --noEmit --strict --skipLibCheck \
  --target esnext --module nodenext --allowImportingTsExtensions \
  investigations/peephole-pair-scans.ts
```

The [experiment](./peephole-pair-scans.ts) loads the pinned optimizer in memory.
Its `git show` command requires local history containing `36eb31d`; fetch that
commit first in a shallow checkout.
It compares that optimizer with an experimental variant that repeats only the
pair scan while list length decreases. It does not import the branch's other
optimizer changes or alter production files. A third variant disables pair
merging to assert that the source corpus actually exercises the pair rule.
The transient loader type assertion describes that compiled module interface;
the compiler's ordinary typed source pipeline is used for the inputs.

The negative source corpus contains 34 functions:

- One through four sequential map lookups.
- `const` declarations and unassigned `let` declarations as mutable controls.
- A later use of the first option value, present or absent.
- An enclosing `if`, present or absent.
- One nested shadowing case.
- One genuinely reassigned `let` option value.

The Cartesian cases contribute 32 functions; the final two are named controls.
The 16 Cartesian `let` cases retain `mutable: true` and exercise rejection of
mutable bindings, not immutable-pair live-name behavior. The script asserts
this flag on the two bindings in `case_2_let_false_false` on both transforms.
The 16 `const` cases exercise immutable bindings.

All source passes strict TypeScript diagnostics and
`extractModule` / `resolveModule` / `narrowModule`, then each backend's
transform. On both backend IRs, first invocation equals second invocation,
and first invocation equals the repeated-scan variant. Disabling pairs changes
the result on both backends, confirming that the comparison exercised merging.
The ordinary const/live/nested cases cover suffix-use and binder conditions;
they do not claim every guard fired in every method.

The separate positive module contains the bare-block and exhaustive switch
sources. For each on each backend, assertions require the affected list to
change from `let, match, let, match` to `let, match, if` and then to `if, if`.
Both final conditions must be `m.has` with the respective original keys, and
the already-merged second lookup must stay unchanged. Full-module assertions
require the repeated-scan output to equal the second complete invocation and
the third invocation to equal the second. The difference counts are computed.

Observed output:

```json
{
  "baseline": "36eb31d",
  "negativeSourceFunctions": 34,
  "positiveSourceFunctions": 2,
  "backendComparisons": 2,
  "backendsExercisingPairMerges": 2,
  "negativeSourceDifferences": 0,
  "supportedPositiveDifferences": 4,
  "syntheticDuplicateNameDifferences": 2
}
```

Set `PAIR_SCAN_EVIDENCE_DIR` to an existing absolute directory to retain the
generated input IR, first output, and second output as JSON for each backend.
Files named `<backend>-<stage>.json` contain the negative corpus; files named
`<backend>-positive-<stage>.json` contain the positive corpus. The synthetic
comparisons remain separate.

## Limits and conditional implementation costs

This is finite testing, not a proof of source-generated idempotence. It uses
optional map-get control flow and does not exhaust loops, annotations, all
shadowing constructs, name sanitization collisions, or imported modules.
It also does not audit every possible interaction with another rewrite.
Pinning `36eb31d` isolates #9's traversal omission; the experiment does not
attribute a constructor/map child change to statement scanning.

The supported positive cases meet the original report's condition for
reconsidering its recommendation. The initial inference from invalid
same-scope duplicate TypeScript declarations overlooked separate source blocks
that extraction flattens. The original retain-the-scan recommendation is
superseded by this evidence.

If the owner approves repetition, list length is a stopping measure: each
successful pass performs at least one two-to-one merge, and a list of length
`n` can undergo at most `n - 1` such merges overall. This does not justify
copying the branch's recursive implementation. Its repeated `slice` and spread
operations copy suffixes and build recursive call stacks. The current iterative
scan already copies suffixes for the live-name check; additional passes would
repeat that work. An iterative repeated loop would avoid recursion between
passes, but would still add scanning and suffix-copying work. No benchmark or
stack-limit measurement was run, so no performance improvement is claimed.

The expected output change is that the earlier lookup also becomes
`if m.has("a")`, removing its temporary option and match in one invocation.
A follow-up should retain the two positive sources on both backends as focused
regressions, along with mutable, distinct-name, live-use, and nested-shadowing
negative controls. It should verify generated backend output as well as IR.

Repeated scanning is one possible change. A suffix-use check that accounts for
rebinding could allow the earlier pair to merge on the first scan, but must
still count references in a later binding's initializer. Preserving lexical
blocks or renaming their variables would change extraction more broadly.
This investigation does not choose or benchmark those alternatives. A new
implementation ticket and owner approval are required before changing the
scan or name handling.
