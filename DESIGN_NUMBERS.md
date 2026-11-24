# DESIGN_NUMBERS — Faithful JavaScript `number` semantics

**Status:** research proposal; no JavaScript-number mode is implemented
**Date:** August 2026
**Updated:** November 2026 (recorded `idealized`-mode progress, Phase 0 `Math.*`/oracle spikes, and Phase 2 Dafny spike results)
**Issue:** [#205](https://github.com/midspiral/LemmaScript/issues/205)

## Decision summary

LemmaScript should eventually expose an enum-shaped project option, not a
boolean:

```json
{
  "number-semantics": "idealized"
}
```

The candidate values are:

| Value | Meaning | Intended use |
|---|---|---|
| `idealized` | Preserve today's mathematical `int`/`nat`/`real` model exactly. | Existing proofs and algorithms whose numeric range is a stated trust assumption. |
| `safe-integer` | Use mathematical integers, but require proof that every source value and intermediate operation agrees with JavaScript safe-integer execution. | A possible lower-cost, faithful subset for integer algorithms. This value should not ship until its obligation and boundary story is designed. |
| `javascript` | Model ECMAScript `Number` values and every supported numeric operation with its JavaScript result. | Code whose behavior depends on rounding, NaN, infinities, signed zero, or the 53-bit precision boundary. |

`idealized` remains the default for backward compatibility. `javascript` is a
semantic commitment, not merely a representation selection. It must be
unavailable for a backend until that backend has passed the conformance and
proof-usability gates in this document. A backend may land first; selecting an
unavailable mode must produce a clear error rather than use idealized
arithmetic.

The `bv64` newtype sketched in issue #205 is not a model of JavaScript
`number`. Bitvector arithmetic wraps modulo 2^64, while JavaScript `Number` is
IEEE-754 binary64: arithmetic rounds, overflow produces infinities, underflow
can produce signed zero, and NaN participates in several distinct equality
relations. A `bv64` may store a floating-point bit pattern, but its arithmetic
operators must never stand for JavaScript arithmetic.

The immediate deliverable is research and executable semantic oracles, not the
config key. Adding the key before an encoding is ready would create a mode whose
name overclaims its fidelity.

## 1. What “faithful” means

For each supported TypeScript numeric construct, translation must commute with
ECMAScript evaluation. Informally, for a supported expression `e` and related
source/backend environments:

```text
decode(evalBackend(translate(e))) = evalECMAScript(e)
```

The relation includes all ECMAScript `Number` values: finite normal and
subnormal values, positive and negative zero, positive and negative infinity,
and the single abstract NaN value. It also includes the operation-specific
observable result: a Boolean for comparison, the correct equality relation for
the calling API, or the correct integer/index conversion.

This is deliberately scoped to the LemmaScript fragment. Features already
excluded from the fragment, such as implicit string-to-number coercion and
dynamic property access, do not become supported merely because the number
model is faithful. Conversely, every numeric construct that remains accepted
in `javascript` mode must be faithful. An unmodeled construct is a diagnostic,
not an opportunity to emit mathematical arithmetic.

This proposal models the ECMAScript language-level Number value. Typed arrays,
`DataView`, and other APIs that expose stored floating-point bytes are outside
the present fragment; adding them would require a separate account of
implementation-defined NaN payloads rather than treating the abstract NaN as a
unique observable bit pattern.

The claim is about the verification model of the production TypeScript. Dafny
or Lean compilation behavior is secondary because LemmaScript executes the
original TypeScript, but the verifier's value identity, collections, and
logical operations still have to match the JavaScript operation being modeled.

## 2. The ECMAScript semantic surface

ECMAScript specifies `Number` as binary64 with all IEEE NaN encodings collapsed
to one language-level NaN. Conversion from an exact mathematical value uses
round-to-nearest, ties-to-even, and preserves the sign on underflow to zero.
That value domain is only the first part of the model; the language defines
operators and library methods individually.

Not every such method has one engine-independent bit result. ECMAScript marks
general exponentiation and many transcendental `Math` functions as
*implementation-approximated*: the specification recommends an ideal result
but delegates the concrete approximation to the implementation. The design
must choose between an engine-neutral relation (sound for every conforming
runtime but possibly weak), an explicit and versioned runtime profile such as a
particular V8 build, or rejecting those functions. The unqualified `javascript`
mode should initially reject them; a Node result alone is not the ECMAScript
standard.

Before implementation, build a checked matrix with one row for every numeric
construct accepted by the resolver. At minimum it must cover:

| Area | JavaScript behavior that must be represented |
|---|---|
| Literals | Decimal, exponent, hexadecimal, binary, and octal literals round to their exact binary64 value. `-0` must survive unary negation. `NaN` and `Infinity` need explicit representations. |
| Arithmetic | `+`, `-`, `*`, `/`, and unary `-` use binary64 results with specified rounding and special-value cases. Each source operation rounds separately. Numeric `+` is in scope; string concatenation and coercion remain separate. |
| Exponentiation | `**` has specified special cases, but its general result is implementation-approximated rather than a uniquely required bit pattern. |
| Remainder | `%` is ECMAScript's truncating remainder with specified NaN, infinity, zero, and sign rules. It is neither integer modulus nor IEEE `remainder`. |
| Ordering | Relational comparisons are unordered on NaN and otherwise use numeric ordering, with the two zeros comparing together. |
| Equality | Numeric `===`, `Object.is`, and SameValueZero differ on NaN and signed zero. Array, Map, and Set operations do not all use the same relation. |
| Truthiness | NaN, `+0`, and `-0` are false; every other Number is true. |
| Classification | `Number.isNaN`, `isFinite`, `isInteger`, and `isSafeInteger` are proof-relevant predicates with distinct definitions. Coercing global variants remain outside the fragment unless modeled separately. |
| Bitwise operations | Operands first undergo `ToInt32` or `ToUint32`; shifts also mask the shift count. `>>>` is not signed arithmetic shift. |
| `Math` | Each admitted member needs its own contract. For example, `Math.round` ties toward positive infinity and preserves signed zero. Many transcendental results are implementation-approximated; min/max and other exact cases have their own NaN and signed-zero rules. |
| Integer conversions | Array access, slice bounds, lengths, and explicit conversions use distinct ECMAScript operations and ranges. Treating every such value as a mathematical `nat` is not faithful. |
| Number-producing APIs | Array/string lengths, Map/Set sizes, `indexOf`/`findIndex`, character-code methods, and other APIs return Numbers even when their inputs are not numeric. Their bounds and sentinel values need bridges rather than an implicit `nat`/`int`. |
| Numeric callbacks | A sort comparator returns a Number; JavaScript interprets negative, positive, zero, and NaN results specially. Callback protocols must not inherit mathematical ordering accidentally. |
| Collections | `includes`, `indexOf`, Map keys, Set elements, sequence equality, and structural record equality must call the intended equality relation rather than inherit the prover's equality accidentally. |
| Strings | Template interpolation and `String(number)` require ECMAScript's number-to-string algorithm, including shortest-round-tripping decimal output. |
| Termination | A raw floating-point value is not a well-founded decreases metric. Termination needs a proved conversion to a mathematical measure. |

This matrix should distinguish three states: faithful and implemented;
explicitly rejected in `javascript` mode; and outside the LemmaScript fragment.
There must be no “accepted but idealized” state.

Useful initial scope is core values, literals, deterministic arithmetic,
comparisons, truthiness, and the exact subset of current `Math` operations whose
contracts have been completed. General exponentiation, implementation-approximated
`Math` functions, bitwise operators, numeric Map/Set keys, and string conversion
can follow, but must be rejected until their rows are complete.

## 3. Current pipeline gaps

Today the semantic decision is spread across the pipeline rather than living at
one emitter boundary:

- [`tools/src/types.ts`](tools/src/types.ts) maps TypeScript `number` to the IR
  integer type; `bigint` is also represented as integer with an extra marker.
- [`tools/src/typedir.ts`](tools/src/typedir.ts) has `nat`, `int`, and `real`, but
  no backend-neutral JavaScript-number kind. Its ordinary numeric literal node
  stores a host JavaScript `number`.
- [`tools/src/extract.ts`](tools/src/extract.ts) and
  [`tools/src/specparser.ts`](tools/src/specparser.ts) convert numeric text with
  `Number(...)`. This obtains a binary64 value but discards the source lexeme
  and does not give the IR a serialization-safe representation of its bits.
  JSON serialization also cannot preserve negative zero, NaN, or infinities;
  after transform folds unary `-`, ordinary string emission prints `-0` as
  `0`.
- [`tools/src/resolve.ts`](tools/src/resolve.ts) chooses among `nat`, `int`, and
  `real`, including real propagation for fractional literals and division.
- [`tools/src/transform.ts`](tools/src/transform.ts) bakes in integer truthiness,
  integer remainder/division helpers, real conversions, and mathematical
  floor/ceiling assumptions.
- The recognized numeric-library surface is not yet one closed list:
  [`tools/src/resolve.ts`](tools/src/resolve.ts),
  [`tools/src/transform.ts`](tools/src/transform.ts), and the emitters now
  handle `Math.abs`, `Math.min` and `Math.max` (1-arg, 2-arg, 3+-arg, and
  `int[]`/`real[]` spreads), `Math.floor`, `Math.ceil`, `Math.trunc`,
  `Math.round` (Dafny reals and both backends for integers), and
  `Number.isSafeInteger` (both integers and Dafny `real`). Acceptance, arity,
  typing, and lowering are still split across passes rather than driven by one
  table, unsupported binary operators (`**`, `**=`, `>>>`, `^`, `^=`) still
  pass through extraction without a dedicated diagnostic (tracked in
  `robertpenner/LemmaScript#30`), and `Math.floor(a / b)` on integers lowers to
  `JSFloorDiv(a, b)`, which differs from JavaScript for quotients above 2^53
  because JavaScript rounds the quotient to binary64 before flooring. Phase 0
  must consolidate acceptance, arity, typing, and lowering before a
  JavaScript-mode support claim is possible.
- [`tools/src/dafny-emit.ts`](tools/src/dafny-emit.ts) maps those mathematical
  types to Dafny. [`tools/src/lean-emit.ts`](tools/src/lean-emit.ts) currently
  rejects real arithmetic rather than modeling floating point.

The implementation therefore needs an explicit backend-neutral `js-number`
kind (exact spelling deferred) threaded through resolve, transform, peephole,
and both emitters. It must not masquerade as `int`, `real`, or `bv64`.

Numeric literals should retain both their source spelling for diagnostics and a
canonical 64-bit binary64 payload for emission and golden tests. The extractor
can compute the payload with the host engine, but tests must cross-check it
against the ECMAScript literal rules. Emitting exact bits avoids depending on a
prover's decimal parser and preserves `-0`. Computed NaNs map to the one
ECMAScript abstract NaN even if a runtime happens to expose a particular NaN
payload.

`bigint` remains mathematically unbounded and separate. A later IR cleanup
should give it a distinct kind instead of an `int` marker, but
`number-semantics` must never change BigInt into binary64 or mix their
operators.

Specification expressions need the same distinction as program expressions.
An annotation such as `result === x + 1` must use JavaScript-number addition
when `x` is a source `number`; otherwise the proof can state the right syntax
with the wrong arithmetic. Ghost variables and helper definitions may still use
mathematical `nat`/`int`/`real`, with explicit checked conversions at the
boundary. Quantification and mixed numeric expressions need corresponding type
rules in the Phase 1 spike.

## 4. `nat`, `int`, and source numbers

In `idealized` mode, `//@ type i nat` and similar annotations keep their current
meaning: they select a mathematical backend type.

That interpretation is unsound in `javascript` mode. A source variable remains
a JavaScript Number even when a proof establishes that its current value is
non-negative and integral. Replacing it with a backend `nat` would make `i + 1`
advance at values where JavaScript addition can round back to `i`.

The target design should separate:

- the runtime representation (`js-number`);
- predicates such as finite, integral, non-negative, safe integer, and valid
  array index;
- an exact mathematical decoding available after the relevant predicate is
  proved; and
- genuinely ghost or compiler-synthetic mathematical `nat`/`int` values.

A non-negative integral Number is not necessarily a safe integer, and a safe
non-negative integer is not necessarily a valid JavaScript array index. These
must not be one refinement. Existing `nat`/`int` source annotations can either
be rejected initially in `javascript` mode or redefined there as refinements
that leave operations on `js-number`; silently retaining their physical-type
meaning is not an option. A dedicated `safe-int`/`safe-nat` annotation may be
clearer, but that surface choice belongs after the refinement spike.

Arrays make the distinction unavoidable. The verifier currently models arrays
as arbitrary mathematical sequences, while JavaScript array length is bounded
and a numeric property is an array element only in the array-index range. A
faithful mode needs bounded-length invariants and proved conversion at each
index, or it must reject source-number indexing. Source reads of array/string
length also produce JavaScript Numbers even if the emitter keeps a separate
mathematical length for proofs. Loop termination similarly uses a decoded ghost
measure, not floating-point order itself.

### What a `safe-integer` mode would promise

If `safe-integer` becomes a public value, it needs a stricter invariant than
`Number.isSafeInteger`. Its mathematical representation would cover only finite
integral values in `[-(2^53 - 1), 2^53 - 1]` and would need to exclude negative
zero. JavaScript regards `-0` as a safe integer, but mapping it to mathematical
zero loses behavior observable through division, `Object.is`, and later
operations.

Inputs and literals must establish that canonical-safe invariant. Each
arithmetic operation must then prove that its JavaScript result is another
canonical safe integer before it can be lowered to the corresponding
mathematical operation. Multiplication by a negative value, remainder of a
negative multiple, division, and unary negation at zero show why range alone is
not enough: they can create `-0`. Division additionally needs an exact integral
quotient, and any operation whose result leaves the safe range is rejected even
when that particular larger integer happens to be representable.

These are verification obligations, not generated assumptions. Entry-point
contracts also need matching runtime guards at the verified/unverified boundary;
otherwise real callers can supply values outside the proved domain. The spike
must prove once, in each backend, that every admitted mathematical lowering
agrees with the JavaScript operation under these invariants. If this becomes
more cumbersome than using `js-number` plus refinements, `safe-integer` should
not become a separate config value.

## 5. Representation choices

| Encoding | Fidelity potential | Proof and implementation cost | Assessment |
|---|---|---|---|
| Native prover binary64 | Exact core arithmetic through SMT floating-point or a kernel model; wrappers can supply ECMAScript-specific operations. | Best starting point, but solver automation for conversions and global arithmetic properties may be weak. Backend versions and APIs are still moving. | Preferred implementation path after backend spikes pass. |
| Raw `bv64` plus verified software floating point | Can be fully faithful when the bits are decoded and every operation implements correct rounding. | Very large arithmetic development; ordinary bitvector `+`, `*`, `/`, and `%` are the wrong operations. | Viable fallback or reference model, not a small newtype change. |
| Algebraic datatype plus exact significand/exponent arithmetic | Makes NaN, infinities, and signed zero explicit and can support mathematical lemmas. | Still requires a verified correct-rounding implementation and may be expensive for SMT and Lean reduction. | Worth a prototype only if native models are unusable. |
| Exact real plus special values (algebraic datatype, no rounding) | Models NaN, infinities, and signed zero faithfully, but uses exact `real` arithmetic with no binary64 rounding or overflow. | Measured as Encoding B on Dafny 4.11.0: strongest symbolic verification rate (528/0/4 isolated batches; 66/66 sampled `Math.*` vectors in 2.56 s), at higher manual hint cost (51 hints) and with `bv32` timeouts. | Candidate intermediate mode or companion specification; does not satisfy binary64 rounding or overflow. |
| Exact real plus special values and a rounding relation | Useful as a specification layer for error proofs. | A relation does not directly give executable, deterministic results; choosing the rounded value is substantial work. | Possible companion proof model, not the primary operational encoding. |
| Uninterpreted operations with axioms | Easy to emit and can state the desired laws. | Moves the hard part into a trusted axiom set and proves little about concrete calculations. | Not acceptable as the default meaning of `javascript`; only an explicitly documented trust mode, if ever. |
| Checked safe-integer abstraction | Faithful for admitted integer computations when operands and results are proved safe and operations such as division satisfy stricter side conditions. | Much easier for existing proofs; excludes fractions, NaN, infinities, signed-zero distinctions, and overflowing/rounding computations. | Useful possible intermediate mode, not a substitute for full `javascript`. |

### Dafny research snapshot

LemmaScript currently pins Dafny 4.11.0. The flags and `newtype uint64 = b:
bv64` experiment in #205 enable a modulo-integer representation, not binary64
semantics.

Dafny merged native `fp32`/`fp64` in `dafny-lang/dafny#6323` (2025-11-07, after
the 4.11.0 release), while the [sound floating-point
PR](https://github.com/dafny-lang/dafny/pull/6514) remains an open draft. The
literal rounding fix `boogie-org/boogie#1141` merged in Boogie (2026-08-20) but
is not yet in the Boogie 3.5.5 bundled with Dafny nightlies.

#### November 2026 Dafny spike results

A comparative spike (`robertpenner/LemmaScript#20`, draft PR
`robertpenner/LemmaScript#29`, commit `6005100`) measured three encodings across
five workloads (safe-integer arithmetic, NaN/signed-zero clamp, signed-zero
equality, `ToInt32`/bitwise operations, and `lerp` plus int/real bridges), 66
sampled `Math.*` vectors, and reproductions of every `dafny-lang/dafny#6514`
defect, using a 30 s per-run limit (one `--isolate-assertions` run and three
seeded whole-file runs):

- **Encoding A (`SafeInt` newtype on pinned Dafny 4.11.0 / `z3-4.12.1`):** 191
  verified, 1 error, 3 timeouts isolated (14 hand-written hints). Fast on
  arithmetic and clamp; timeouts sit in `bv32` round-trips. Cannot represent
  NaN, infinities, `-0`, or fractions.
- **Encoding B (algebraic extended `real` + `-0` flag / `PosInf` / `NegInf` /
  `NaN` on pinned Dafny 4.11.0 / `z3-4.12.1`):** 528 verified, 0 errors, 4
  timeouts isolated (51 hand-written hints to unfold the datatype); 66/66
  sampled `Math.*` vectors verify in 2.56 s. Timeouts occur in `bv32` concrete
  examples and occasionally in seeded `Midpoint`. Arithmetic is exact real
  without rounding or overflow.
- **Encoding C (native `fp64` on nightly `4.11.1+a869244` / `z3-4.16.0`, repros
  also run on `z3-4.12.1`):** 200 verified, 7 errors, 58 timeouts isolated (16
  hints). Concrete facts and all 66 sampled `Math.*` vectors verify quickly
  (2.90 s), and it proves real JavaScript counterexamples such as
  `lerp(-MAX_VALUE, MAX_VALUE, 0)` evaluating to NaN. Symbolic range, order,
  and conversion proofs routinely time out or report errors on true statements.

Answers to the six spike questions:

1. **Exact bit-pattern construction and classification:** Nightly `fp64`
   supports classification (`IsNaN`, `IsInfinite`, `IsFinite`, `IsNormal`,
   `IsSubnormal`, `IsZero`, `IsPositive`, `IsNegative`) and IEEE constants.
   Bit-pattern casts (`x as bv64` and `b as fp64`) are rejected at resolution.
   Finite values can be emitted as exact decimal expansions (all 66 sampled
   vectors, including subnormal `-5e-324`, verified). `fp64` is absent in
   tagged Dafny 4.11.0.
2. **Total IEEE APIs:** Nightly static methods (`fp64.Add`, `Sub`, `Mul`,
   `Div`, `Neg`, `Less`, `LessOrEqual`, `Greater`, `GreaterOrEqual`, `Equal`)
   are total with round-to-nearest-even. Surface operators carry obligations
   that are checked inconsistently: for finite nonzero `x`, `x / 0.0` reports
   possible division by zero while `x / -0.0` verifies without error. `Abs`,
   `Sqrt`, `Min`, `Max`, `Floor`, `Ceiling`, and `Round` require non-NaN
   arguments, and `fp64.Round` ties to even instead of JavaScript's ties toward
   `+Infinity`, so JavaScript `Math.*` requires explicit wrappers.
3. **Equality for `===`:** `fp64.Equal` matches `===` (NaN unequal to itself,
   `+0 == -0`). Ghost `==` matches `Object.is`. Compiled `==` rejects NaN and
   mixed signed zeros. Surface `<=` disagrees with ghost `==` on signed zeros
   (`0.0 <= -0.0 && -0.0 <= 0.0 && 0.0 != -0.0` verifies, breaking
   antisymmetry).
4. **Library helpers (`%`, conversions, rounding, SameValueZero):** SameValueZero,
   `Math.min`/`max`, `Math.trunc`, and `Math.round` (comparing distance from
   `Floor(x)` instead of `Floor(x + 0.5)`, which fails on
   `0.49999999999999994`) verified 66/66 sampled vectors in both B and C.
   `ToInt32` via `fp64.ToInt(x) % 2^32` and `bv32` round-trips through `int`
   timed out or errored on symbolic inputs in every encoding. An `fp64` `%`
   helper was not written.
5. **Proof stability under repeated isolated and whole-file runs:** Encodings A
   and B are stable on arithmetic, clamp, and signed-zero workloads (with
   seed-sensitive variance near the 30 s limit on `bv32` and `B_safeint`
   `Midpoint`). Encoding C fails the usability bar: every workload file other
   than `C_lib` hits timeouts in every run, `fp64.Less`/`LessOrEqual`
   trichotomy and transitivity time out under both Z3 4.12.1 and Z3 4.16.0, and
   true `fp64.FromReal` facts report verifier errors or timeouts. In addition,
   a type synonym `type F = fp64` crashes Dafny on the first literal, and
   `dafny build -t js` crashes or miscompiles `fp64` (though LemmaScript does
   not rely on Dafny's JavaScript compiler).
6. **Minimum Dafny version and flags:** Encodings A and B run on pinned Dafny
   4.11.0 with no extra flags. Encoding C requires a post-`#6323` build (no
   tagged release yet) and fails the Phase 2 soundness gate: every pre-fix
   defect tracked in `dafny-lang/dafny#6514` reproduced on the nightly (`as
   int` clamping to `[-2^63, 2^63)`, `fp32.E` error, newtype `as real` skipping
   finiteness, crash on unresolved fp literals, loop interval unsoundness, `/`
   by `-0.0`, `fp.to_real` timeouts), and `boogie-org/boogie#1141` (1-ULP
   literal rounding) reproduced under bundled Boogie 3.5.5.

**Current Dafny verdict:** Native `fp64` does not pass the Phase 2 gate today
because of open upstream soundness bugs (`dafny-lang/dafny#6514`, Boogie 3.5.5)
and widespread symbolic solver timeouts. Do not bind LemmaScript to nightly
`fp64`; re-run the spike after a tagged Dafny release ships `#6514` and a newer
Boogie.

Compilation support in Dafny is not a release blocker for LemmaScript, but any
verification unsoundness, identity mismatch, or solver inability is.

### Lean research snapshot

The original research snapshot used Lean 4.24, where `Float` was opaque to useful
logical reasoning. Lean merged [`Float.Model`](https://github.com/leanprover/lean4/pull/14079)
and connected `Float` to it in a follow-up in June 2026, but that work is newer
than that earlier toolchain. The [development
manual](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/)
describes a canonical-NaN `UInt64` model with logical definitions for a core set
of operations, while warning that it is not a general floating-point theorem
library and that some operations remain opaque.

The Velvet 2 checkout now pins Lean 4.34.0 in `lean-toolchain`. A partial
inventory (`robertpenner/LemmaScript#23`, draft PR `#28`, `599ee04`) checked
`Math.*` against Lean 4.34.0 and Mathlib (`Divergences.lean`):

- Core operations (`Float.abs`, `Float.sqrt`, comparisons, arithmetic) are
  `Float.Model`-backed `def`s; transcendental `Math.*` functions (`pow`, `exp`,
  `log`, trigonometry) remain `opaque` C externs.
- Several Lean `Float` operations diverge from ECMAScript: `Float.pow` returns
  `1` where JavaScript returns `NaN` (`±1 ** ±Infinity`, `1 ** NaN`); `min` and
  `max` use `minOfLe`/`maxOfLe`, making NaN and `±0` results depend on argument
  order; and `Float.round` rounds `-2.5` to `-3` and `-0.5` to `-1`.
- Mathlib `ℝ` diverges from JavaScript on out-of-domain finite inputs
  (`0 ^ (-1) = 0`, `√(-1) = 0`, `log 0 = 0`, `log (-1) = 0`, and finite values
  for negative bases with non-integral exponents).

The full Lean `Float.Model` workload spike (`robertpenner/LemmaScript#22`) and
Lean Mathlib `real` prototype (`robertpenner/LemmaScript#21`) are currently on
the back burner and have not been run; upstream Lean closure soundness bug
`midspiral/LemmaScript#267` also remains open. When resumed, the Lean spike
must still answer:

1. Which source operations reduce in the kernel and which remain opaque.
2. Whether Velvet 2's generated VCs and `finish` can use the model without
   unacceptable proof size or time.
3. How propositional equality, `BEq`, ordering, and hashed collections line up
   with the three ECMAScript equality relations.
4. Whether literal construction from exact bits is available and convenient.
5. Which separate floating-point theorem library, if any, is suitable for error
   bounds and how its results transfer to `Float.Model`.
6. The cost of any further Lean/Velvet upgrades and changes to the checked-in proofs.

Until this passes, `number-semantics: "javascript"` under Lean must be rejected.

## 6. Configuration and composition

The proposed registry entry is an enum with `default: "idealized"`. It should be
config-only (`fileOverride: false`) initially. Number semantics changes every
numeric signature and proof, so a casual per-file `//@ option` creates an ABI-like
problem: a caller could reinterpret an imported callee's `number` under its own
mode.

The implementation must resolve the option for every source file in a checked
dependency closure and reject mismatches, including mismatches caused by nested
`lemmascript.json` files. An explicit future bridge could expose an idealized
function to a JavaScript-number caller with conversion/refinement obligations;
auto-extern must not invent that bridge.

Generated artifacts should record a non-default semantic mode, for example:

```text
// lsc options: number-semantics=javascript
```

The marker makes a hand-carried proof artifact auditable and allows `lsc check`
to enforce the backend capability and version that produced it. Switching modes
is a normal source/config change: Dafny users run `lsc regen`, preserving proof
additions, and then repair proofs against the intentionally different model.

The implementation must also pin a normative ECMAScript snapshot and Test262
revision. The public value can remain `javascript`, but the artifact should
carry an internal model revision (for example, `ecma262-2026-v1`) so a later
specification or helper change cannot silently alter a standalone proof. A
runtime-specific profile, if one is ever supported for implementation-approximated
operations, additionally pins the engine and version.

## 7. Conformance oracle and test plan

The first implementation artifact should be a Node-based oracle, independent of
either emitter. It records both observable results and raw binary64 bits using a
`DataView`. Pin and adapt the relevant cases from TC39's Test262 rather than
inventing every edge case locally; supplement them with a compact LemmaScript
table that can be emitted to either prover. The corpus should contain at least:

- `+0`, `-0`, canonical and computed NaN, and both infinities;
- the smallest subnormal, largest subnormal, smallest normal, and largest finite
  values;
- neighbors of 2^53 and -2^53;
- halfway rounding cases, cancellation, gradual underflow, and overflow;
- division and remainder by both zeros and infinities;
- every equality relation over a boundary-value cross product;
- `ToInt32`/`ToUint32`, shifts, supported `Math` operations, truthiness, and
  supported collection operations; and
- randomized operand pairs, with failures saved as permanent regression cases.

For each supported operation, generate the same table in Dafny or Lean and check
it against the Node oracle. Compare bits with `Object.is`-aware handling rather
than decimal printing alone, canonicalizing all NaN payloads to the one
ECMAScript NaN value. Differential tests establish conformance on a large
corpus; the backend model or solver theory supplies the universal semantics.
Neither one replaces the other. Node can only be an oracle for deterministic
ECMAScript operations or for an explicitly named Node/V8 runtime profile; it
cannot select the universal result of an implementation-approximated operation.
For the deterministic IEEE core, triangulate suspicious failures against
Berkeley SoftFloat/TestFloat rather than treating a single engine as an
independent specification.

Keep a second proof-usability suite. It should exercise the kinds of properties
LemmaScript users need: safe range preservation, monotonicity under explicit
finite/range hypotheses, exact integer increments, error bounds, array-loop
invariants, NaN-sensitive branches, and composition across helper functions.
Repeat runs matter because a model that is semantically sound but routinely
times out is not a usable backend.

## 8. Research order and acceptance gates

### Phase 0 — semantic inventory

1. Enumerate every numeric syntax/operator/builtin currently accepted by extract
   and resolve.
2. Give each one a normative ECMAScript rule and one of the three support states
   from §2.
3. Audit the applicable Test262 cases, then build the Node bit/equality oracle
   and boundary corpus at pinned revisions.
4. Classify implementation-approximated operations and choose rejection,
   engine-neutral relations, or explicit runtime profiles for each family.
5. Define the source-to-backend relation and the trusted computing base in a
   short, reviewable form.

**Gate:** no accepted construct lacks a specified translation or an explicit
diagnostic.

*Progress (November 2026):* Two Phase 0 artifacts exist in fork draft PRs
awaiting upstream layout and review decisions: a normative ECMAScript 2026
`Math.*` matrix (12 exact vs. 14 implementation-approximated members) with
1,487 deterministic Node vectors (`robertpenner/LemmaScript#28`), and a
standalone Node `DataView` binary64 conformance oracle with 2,548 vectors
across 12 families, raw NaN payload preservation plus canonicalization, and 16
curated Test262 cases (`robertpenner/LemmaScript#39`, cross-checked with 0
mismatches against `#28` and 162 verified / 0 errors against `#29` Encoding B).
A companion fix rejecting unsupported binary operators (`**`, `**=`, `>>>`,
`^`, `^=`) at extraction is in draft `robertpenner/LemmaScript#38`.

### Phase 1 — IR and refinement spike

1. Preserve numeric literal spelling and exact bits.
2. Prototype a `js-number` IR kind without changing idealized output.
3. Define finite/integer/safe/index predicates and exact decoding.
4. Decide the `nat`/`int` annotation behavior, sequence-length bound, indexing
   obligations, and decreases bridge.
5. Decide whether `safe-integer` earns a public config value or remains a set of
   refinements within `javascript` mode.

**Gate:** existing examples regenerate byte-for-byte in `idealized`, and the
refinement story does not prove source operations with mathematical arithmetic.

### Phase 2 — independent backend spikes

Implement only literals, classification, core arithmetic, comparisons, the
three equality relations, and truthiness against released/pinned backend
versions. Cross-check the oracle, then run the proof-usability suite. Do not yet
add the public config key.

**Gate:** exact conformance on the golden corpus, no trusted per-operation axioms,
no known verifier unsoundness, stable proof times, and an identified minimum
backend version.

*Progress (November 2026):* The Dafny Phase 2 spike (`robertpenner/LemmaScript#29`)
completed and found that native `fp64` does not pass this gate on current
toolchains (see §5). The Lean Phase 2 spike (`robertpenner/LemmaScript#22`) is
currently deferred on the back burner.

### Phase 3 — one backend behind the option

Add the registry entry, option flow, artifact marker, hard errors for unsupported
constructs/backends, dependency-mode checks, and focused documentation. Dafny
may land before Lean if it passes first. `idealized` remains byte-for-byte
unchanged.

**Gate:** `lsc check` cannot silently verify a JavaScript-mode file with
idealized operations, even through a builtin, collection, cross-file call, or
hand-carried artifact.

### Phase 4 — broaden the faithful fragment

Add `%`, conversions/indexing, the supported `Math` surface, bitwise operators,
numeric collection behavior, and string conversion one reviewed family at a
time. Each family lands with its normative matrix rows, Node oracle cases, and
backend proofs.

## 9. Open decisions

1. Is `safe-integer` valuable enough to be a semantic mode, or should safe
   integers be refinements inside `javascript` mode?
2. In JavaScript mode, should existing `nat`/`int` annotations become runtime
   Number refinements or fail in favor of explicit `safe-nat`/`safe-int` names?
3. May the initial release be Dafny-only, with a hard Lean error, or is backend
   parity required before exposing the option?
4. Which operation families form the minimum useful JavaScript-mode fragment?
5. Are numeric keys/elements in Map and Set initially prohibited, or do custom
   SameValueZero containers belong in the first release?
6. Is a separate mathematical floating-point library needed for meaningful
   error proofs, or is exact operational verification the initial goal?
7. Should implementation-approximated operations stay unsupported, use a weak
   engine-neutral relation, or require a separately versioned runtime profile?
8. While native Dafny `fp64` remains blocked on upstream soundness and solver
   stability, is an unrounded `extended-real` mode (Encoding B: exact `real`
   plus `-0`, `±Infinity`, and `NaN`) worth offering as an intermediate option,
   or should LemmaScript skip it and wait for faithful binary64?

## Primary references

- [ECMAScript 2026 §6.1.6.1, The Number Type](https://tc39.es/ecma262/2026/multipage/ecmascript-data-types-and-values.html#sec-ecmascript-language-types-number-type)
- [ECMAScript 2026 §4.4.1, implementation-approximated](https://tc39.es/ecma262/2026/multipage/overview.html#sec-terms-and-definitions-implementation-approximated)
- [ECMAScript 2026 §7.1, Type Conversion](https://tc39.es/ecma262/2026/multipage/abstract-operations.html#sec-type-conversion)
- [ECMAScript 2026 §21.3, The Math Object](https://tc39.es/ecma262/2026/multipage/numbers-and-dates.html#sec-math-object)
- [TC39 Test262, the official ECMAScript conformance suite](https://github.com/tc39/test262)
- [SMT-LIB floating-point theory](https://smt-lib.org/theories-FloatingPoint.shtml)
- [Dafny reference manual, floating-point types](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-floating-point-types)
- [Dafny PR #6323, initial `fp32`/`fp64` support](https://github.com/dafny-lang/dafny/pull/6323)
- [Dafny PR #6514, sound `fp32`/`fp64` verification](https://github.com/dafny-lang/dafny/pull/6514)
- [Boogie PR #1141, decimal float literal rounding fix](https://github.com/boogie-org/boogie/pull/1141)
- [Lean floating-point reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/)
- [Lean PR #14079, `Float.Model`](https://github.com/leanprover/lean4/pull/14079)
