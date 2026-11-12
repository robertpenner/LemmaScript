# Do statement-pair scans need repeated passes?

Investigation for [robertpenner/LemmaScript#8](https://github.com/robertpenner/LemmaScript/issues/8).

## Recommendation

Retain the current scan. The bounded supported-source experiment found no
first/second-invocation difference and no difference from repeated scanning on
either backend. A synthetic duplicate-binding example does change, but does not
establish a current source-generation defect. No production scanning algorithm
changes in this investigation.

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

Two same-scope `const x` declarations are invalid TypeScript. Source shadowing
inside an `if` is valid and was tested separately: child lists are optimized
before the enclosing list's suffix check, so that case did not require a second
outer scan. No supported same-list duplicate-binding producer was found in the
tested lowering paths. This investigation does not prove that none exists in
every supported source construct.

## Reproducible experiment

From the repository root, with the compiler development dependencies installed:

```sh
node --import tsx investigations/peephole-pair-scans.ts
node node_modules/typescript/bin/tsc --noEmit --strict --skipLibCheck \
  --target esnext --module nodenext --allowImportingTsExtensions \
  investigations/peephole-pair-scans.ts
```

The [experiment](./peephole-pair-scans.ts) loads the pinned optimizer in memory.
It compares that optimizer with an experimental variant that repeats only the
pair scan while list length decreases. It does not import the branch's other
optimizer changes or alter production files. A third variant disables pair
merging to assert that the source corpus actually exercises the pair rule.
The transient loader type assertion describes that compiled module interface;
the compiler's ordinary typed source pipeline is used for the inputs.

The source corpus contains 34 functions:

- One through four sequential map lookups.
- `const` and unassigned `let` declarations.
- A later use of the first option value, present or absent.
- An enclosing `if`, present or absent.
- One nested shadowing case.
- One genuinely reassigned `let` option value.

The Cartesian cases contribute 32 functions; the final two are named controls.
All source passes strict TypeScript diagnostics and
`extractModule` / `resolveModule` / `narrowModule`, then each backend's
transform. On both backend IRs, first invocation equals second invocation,
and first invocation equals the repeated-scan variant. Disabling pairs changes
the result on both backends, confirming that the comparison exercised merging.
The ordinary const/let/live/nested cases cover the suffix-use and binder
conditions; they do not claim every such guard fired in every generated method.

Observed output:

```json
{
  "baseline": "36eb31d",
  "sourceFunctions": 34,
  "backendComparisons": 2,
  "backendsExercisingPairMerges": 2,
  "sourceDifferences": 0,
  "syntheticDuplicateNameDifferences": 2
}
```

Set `PAIR_SCAN_EVIDENCE_DIR` to an existing absolute directory to retain the
generated input IR, first output, and second output as JSON for each backend.
The current script asserts deep equality of those full modules, not merely
statement counts. The synthetic comparisons are separate from that corpus.

## Limits and conditional implementation costs

This is finite testing, not a proof of source-generated idempotence. It uses
optional map-get control flow and does not exhaust loops, annotations, all
shadowing constructs, name sanitization collisions, or imported modules.
It also does not audit every possible interaction with another rewrite.
Pinning `36eb31d` isolates #9's traversal omission; the experiment does not
attribute a constructor/map child change to statement scanning.

If a future supported-source example produces the duplicate-name mechanism
or another disappearing live reference, first record its complete lowering and
name scopes. That is the specifically unresolved question that could reverse
this recommendation.

If repetition becomes warranted, list length is a stopping measure: each
successful pass performs at least one two-to-one merge, and a list of length
`n` can undergo at most `n - 1` such merges overall. This does not justify
copying the branch's recursive implementation. Its repeated `slice` and spread
operations copy suffixes and build recursive call stacks. The current iterative
scan already copies suffixes for the live-name check; additional passes would
repeat that work. An iterative repeated loop would avoid recursion between
passes, but would still add scanning and suffix-copying work. No benchmark or
stack-limit measurement was run, so no performance improvement is claimed.

The owner may retain the existing scan on this evidence. A new implementation
ticket requires a supported reproducer or a separately approved stronger
normalization contract for arbitrary public IR.
