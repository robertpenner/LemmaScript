# Dafny number-encoding spike (fork issue #20)

This spike compares three ways to give LemmaScript-generated Dafny the
semantics of JavaScript `number`, on the workloads named in issue #20 and
DESIGN_NUMBERS.md §8 Phase 2:

- Encoding A, SafeInt: `newtype SafeInt = x: int | -(2^53-1) <= x <= 2^53-1`
  on pinned Dafny 4.11.0. It has no NaN, no infinities, no `-0` and no
  fractions. Library: `corpus/A_lib.dfy`.
- Encoding B, algebraic extended real: a datatype holding an exact `real`
  plus a negative-zero flag, `PosInf`, `NegInf` and `NaN`, on pinned Dafny
  4.11.0. Arithmetic is exact; there is no rounding and no overflow.
  Library: `corpus/B_lib.dfy`.
- Encoding C, native `fp64`: IEEE binary64 from dafny-lang/dafny#6323, on a
  Dafny nightly. JavaScript operators are wrapped in the unchecked static
  methods (`fp64.Add`, `fp64.Equal`, `fp64.Less`, ...). Library:
  `corpus/C_lib.dfy`.

Every number below comes from the run recorded in `results/`. Anything the
spike did not run is marked "not measured". This report does not recommend
an encoding.

## Toolchains and method

From `results/versions.txt` (run started 2026-11-19T16:26:26Z on Darwin
arm64, 10 logical cpus, Node v24.17.0):

| | Pinned (A, B) | Nightly (C, repros) |
|---|---|---|
| `dafny --version` | 4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2 | 4.11.1+a8692441e735a865c378c76e87bcf7d0e6c7c592 (release nightly-2026-11-02-a869244) |
| Boogie (`Boogie.ExecutionEngine` in `DafnyDriver.deps.json`) | 3.5.5 | 3.5.5 |
| Bundled Z3 | z3-4.12.1, z3-4.14.1 | z3-4.12.1, z3-4.16.0 |
| Prover actually used (`verify --boogie -trace`, "Using prover") | z3-4.12.1 | z3-4.16.0 |

The corpus runs use each toolchain's default prover. Each repro runs twice
on the nightly, once per bundled Z3, selected with `--solver-path`.

The recorded run was:

```sh
cd spikes/dafny-number-encodings
DAFNY_FP=<nightly>/dafny/dafny \
VECTORS=<LemmaScript checkout>/spikes/math-semantics/vectors/math-special-values.json \
./run.sh
```

`DAFNY` defaults to the `dafny` on PATH (the pinned 4.11.0). In the
recorded run `<nightly>` was the coordinator's scratch download
`.../run-6WMCfLu3/dafny-nightly`. Without `VECTORS` the vectors section is
skipped and the skip is written to `results/vectors.csv`. `SECTIONS` selects
a subset of `verify repro js vectors`.

For each corpus file `run.sh` does:

- one isolated run: `dafny verify --allow-warnings
  --verification-time-limit 30 --isolate-assertions --log-format csv;...`
  with `--library corpus/<X>_lib.dfy`. Output in `results/verify/`.
- three whole-file runs, `--boogie -randomSeed:1`, `:2` and `:3`, with the
  same time limit. Output in `results/seeds/`.

`results/summary.csv` holds the verifier's own "N verified, N errors, N time
outs" line for every run, the wall-clock seconds, and the counts of
`// @manual` (hand-written assertions and calls to helper lemmas) and
`// @lemma` (helper lemma declarations) in the file. In isolated runs the
counts are per assertion batch; in whole-file runs they are per Boogie
implementation, so the two are not comparable with each other.

The verification time limit was 30 s for every run. A timeout is counted as
a finding, never retried with a larger limit.

## Workloads and results

The workloads follow issue #20. W3 (signed zero) and W5 (lerp and
representation bridges) do not exist in Encoding A, which has no `-0` and no
fractions.

- W1 `*_safeint`: midpoint, binary search, bounded sum.
- W2 `*_clamp`: clamp written with `<`/`>` guards, with negated guards
  (`!(x >= lo)`), and with `Math.min`/`Math.max`.
- W3 `*_signedzero`: `Object.is`, SameValueZero, `-0` through clamp and
  addition, map-key normalization.
- W4 `*_bitwise`: `x | 0`, `x >>> 0`, `Math.imul`, `a & b`, `x >>> n`.
- W5 `*_lerp`: `a + t * (b - a)` and int/real bridges.

Counts are verified, errors, time outs. "s" is wall-clock seconds.

| File | Isolated | s | Seed 1 | Seed 2 | Seed 3 | @manual | @lemma |
|---|---|---|---|---|---|---|---|
| A_lib | 8, 0, 0 | 4.91 | 5, 0, 0 | 5, 0, 0 | 5, 0, 0 | 1 | 1 |
| A_safeint | 95, 1, 0 | 17.37 | 7, 0, 0 | 7, 0, 0 | 6, 0, 1 | 3 | 1 |
| A_clamp | 14, 0, 0 | 12.44 | 6, 0, 0 | 6, 0, 0 | 6, 0, 0 | 0 | 2 |
| A_bitwise | 73, 0, 3 | 42.56 | 11, 0, 3 | 11, 1, 2 | 11, 0, 3 | 8 | 6 |
| B_lib | 77, 0, 0 | 7.62 | 16, 0, 0 | 16, 0, 0 | 16, 0, 0 | 0 | 0 |
| B_safeint | 205, 0, 0 | 33.55 | 17, 0, 1 | 17, 0, 1 | 18, 0, 0 | 14 | 6 |
| B_clamp | 27, 0, 0 | 3.80 | 8, 0, 0 | 8, 0, 0 | 8, 0, 0 | 0 | 5 |
| B_signedzero | 46, 0, 0 | 4.61 | 10, 0, 0 | 10, 0, 0 | 10, 0, 0 | 0 | 8 |
| B_bitwise | 42, 0, 2 | 34.63 | 13, 0, 1 | 13, 0, 1 | 14, 0, 0 | 6 | 7 |
| B_lerp | 71, 0, 0 | 7.07 | 15, 1, 0 | 15, 1, 0 | 15, 1, 0 | 12 | 9 |
| C_lib | 5, 0, 0 | 2.39 | 3, 0, 0 | 3, 0, 0 | 3, 0, 0 | 0 | 0 |
| C_safeint | 59, 0, 28 | 189.53 | 3, 1, 2 | 3, 1, 2 | 3, 1, 2 | 1 | 0 |
| C_clamp | 8, 0, 4 | 31.21 | 2, 0, 3 | 2, 0, 3 | 2, 0, 3 | 0 | 5 |
| C_signedzero | 21, 0, 1 | 33.41 | 7, 0, 1 | 7, 0, 1 | 7, 0, 1 | 0 | 8 |
| C_bitwise | 29, 1, 11 | 95.89 | 6, 0, 7 | 6, 0, 7 | 6, 0, 7 | 4 | 7 |
| C_lerp | 17, 1, 6 | 64.09 | 5, 0, 4 | 5, 0, 4 | 5, 0, 4 | 0 | 5 |

Hint totals across the encoding's files: A has 12 `@manual` and 10
`@lemma`; B has 32 and 35; C has 5 and 25. The hint counts measure what the
author wrote, not how much effort each encoding would need to verify fully:
the A and B files were iterated until they verified, while the C files keep
the hints that were tried and still time out.

Where the failures are, from `results/verify/*.csv` (isolated batches that
did not pass, per procedure) and the `Error` lines in `results/verify/*.out`
and `results/seeds/*.out`:

- A_safeint, isolated: one error, `result of operation might violate
  newtype constraint for 'SafeInt'` at `s := s + a[i]` (74,11) in
  `SumBounded` (33 of 34 batches pass). The same procedure verifies in the
  seed 1 and seed 2 whole-file runs and times out in seed 3.
- A_bitwise: `Bv32RoundTrip`, the lemma `(x as bv32) as int == x` for
  `0 <= x < 2^32`, times out in every run. In the isolated run `Examples`
  times out at `assert And(-1, 255) == 255` (90,2) and `assert UshrN(-1,
  28) == 15` (92,2), the two concrete assertions that go through `bv32`. Whole-file, `AndWithSelf`
  times out under every seed, and seed 2 reports `assertion might not hold`
  at `assert And(-1, 255) == 255` (90,2) where seeds 1 and 3 time out.
- B_safeint: `Midpoint` times out whole-file under seeds 1 and 2 and
  verifies under seed 3 and in isolation.
- B_bitwise: `AndExample` and `UshrExample`, which state `-1 & 255` and
  `-1 >>> 28` on concrete values through `bv32`, each time out in one
  isolated batch; `AndExample` times out whole-file under seeds 1 and 2.
- B_lerp: every isolated batch passes (71 of 71). Every whole-file run
  reports `assertion might not hold` at `assert 0.0 <= m.r <= d.r` (49,20),
  a hand assertion inside `LerpInRange`.
- C_safeint: `Midpoint` well-formedness 0 of 6 batches pass, `BinarySearch`
  25 of 42, `SumBounded` 23 of 28; all 28 failures are timeouts. Whole-file,
  `Midpoint` and `BinarySearch` time out and the `SumBounded` invariant
  `(s as real) <= (i as real) * (bound as real)` (63,26) is reported as not
  maintained under all three seeds.
- C_clamp: `ClampInRange` (1 of 3 batches), `ClampNegInRange` (2 of 3) and
  `GuardsAgreeOffNaN` (0 of 1) time out. The concrete NaN and `-0` facts
  about clamp verify.
- C_signedzero: `NormKeyCollapses`, that SameValueZero equals `Object.is`
  after mapping `-0` to `+0`, times out. `ObjectIsIsIdentity` and the
  other signed-zero lemmas verify.
- C_bitwise: `OrZeroSpecials` (1 of 5 batches), `OrZeroRange` (1 of 3),
  `OrZeroIdempotent`, `ImulExamples`, `Ushr0Examples`, `AndExample` and
  `UshrExample` fail; 11 are timeouts. The one error is `ensures
  OrZero(fp64.NaN) == 0.0` (36,27). JavaScript has `NaN | 0 === 0`, and
  `OrZero(NaN)` is `fp64.FromReal(0 as real)` in this corpus, so the claim
  is true; repro R14 shows that the verifier also reports errors on true
  `FromReal` claims. Whether this one is a false claim or an incomplete
  proof was not determined.
- C_lerp: `LerpExtremesIsNaN` verifies (Encoding C proves that
  `lerp(-MAX_VALUE, MAX_VALUE, 0)` is NaN). `LerpAtOneOvershoots` (1 of 2
  batches), `LerpEndpointsSmallInts`, `BridgeRoundTrip` and `BridgeAdd`
  fail; the one error is `BridgeAdd`'s `Add(x, y) as real == x as real + y
  as real` (62,50) for safe integers whose sum is safe, which is a true
  statement about IEEE addition.

## Answers to DESIGN_NUMBERS.md §5

### 1. Whether exact bit-pattern construction and classification are supported.

Classification is supported. `fp64` values have the members `IsNaN`,
`IsInfinite`, `IsFinite`, `IsNormal`, `IsSubnormal`, `IsZero`,
`IsPositive` and `IsNegative`, and the type has the constants `NaN`,
`PositiveInfinity`, `NegativeInfinity`, `MinValue`, `Pi` and `E`. The C
corpus uses them throughout; C_lib and the classification lemmas in
C_signedzero verify.

Exact bit-pattern construction is not supported. Repro R13 is rejected at
resolution with "type conversion to a bitvector-based type is allowed only
from numeric and bitvector types, char, and ORDINAL (got fp64)" for
`x as bv64` and "type conversion to fp64 is allowed only from numeric types
(int, real, fp32, fp64) (got bv64)" for `b as fp64`. Conversions go
through `int` or `real`, which cannot carry a NaN payload or the sign of
zero. A finite value can be written exactly as a decimal literal: the
vectors generator writes every operand as the exact decimal expansion of
its bit pattern, and all 66 C vector lemmas verify, including the subnormal
`-5e-324`. Encoding A has no non-integer values. Encoding B classifies by
datatype constructor and the `negZero` flag and has no bit patterns.

On pinned Dafny 4.11.0 the type does not exist: P01 fails with "Type or
type parameter is not declared in this scope: fp64".

### 2. Which APIs produce total IEEE results. Dafny surface operators may impose well-formedness obligations that exclude NaN-producing cases; JavaScript arithmetic must use total/unchecked operations or wrappers instead.

In the nightly, the static methods `fp64.Add`, `Sub`, `Mul`, `Div`,
`Neg`, `Less`, `LessOrEqual`, `Greater`, `GreaterOrEqual` and `Equal` are
total and follow IEEE 754 round-to-nearest-even. C_lib wraps every
JavaScript operator in them, and C_lib verifies with no obligations at the
call sites. The surface operators `+ - * /` and `< <= > >=` carry
obligations. Repro R07 shows them: `x / -0.0` for non-NaN `x` reports "fp64
division has invalid operand combination (e.g., ∞+(-∞), ∞*0, 0/0, ∞/∞)",
and `x / 0.0` reports that and "possible division by zero" as well.
`fp64.FromReal` rounds; `as fp64` requires the value to be exactly
representable; `fp64.ToInt` truncates and requires a finite argument;
`Abs`, `Sqrt`, `Min`, `Max`, `Floor`, `Ceiling` and `Round` require
non-NaN arguments, so JavaScript's `Math.min`, `Math.max`, `Math.trunc` and
`Math.round` are written in C_lib with explicit NaN and `-0` cases.

Encoding B's operations are total by construction (every `match` case
returns a value) but are exact real arithmetic: B does not round and never
overflows to infinity. B_lerp proves `LerpInRange`, `LerpAtOne` and
`LerpExtremesInB`, all of which JavaScript violates (the counterexamples
are written next to each lemma). Encoding A is total on `SafeInt` only;
every operation that can leave the safe range carries a newtype obligation,
which is the A_safeint error above.

### 3. Which equality represents numeric `===`. Dafny value identity intentionally distinguishes signed zero and identifies NaN, so it cannot stand in for all JavaScript equality contexts.

`fp64.Equal` is IEEE equality and matches `===`: NaN is unequal to itself
and `+0` equals `-0`. C_lib uses it for `StrictEq`. Ghost `==` on `fp64` is
identity (NaN equals NaN, `+0` differs from `-0`), which matches
`Object.is`; C_signedzero's `ObjectIsIsIdentity` verifies that the compiled
`ObjectIs` in C_lib agrees with it. Compiled `==` requires both operands to
be non-NaN and not a pair of differently signed zeros, so it is unusable as
`===` in general.

The surface ordering operators disagree with ghost `==` on signed zeros.
In repro R05, `SignedZeroWitness` verifies `p <= n && n <= p && p != n`
for `p = 0.0` and `n = -0.0`, and `Antisymmetry` (`a <= b && b <= a ==> a
== b` for non-NaN `a`, `b`) fails. dafny#6514 lists this as an
incoherence it fixes.

In Encoding B, `StrictEq` is a predicate written for `===` and `ObjectIs` is
datatype `==`. In Encoding A, `===` is `int` equality.

### 4. How to implement ECMAScript `%`, conversions, rounding functions, and SameValueZero when no native operation matches.

The spike wrote each of these as a library function:

- `%`: B_lib `Rem` truncates the exact quotient with `TruncReal` and
  gives a zero result the dividend's sign. A_lib `JSRem` and `JSTruncDiv`
  work on `int` with a `d != 0` precondition. `fp64` has no remainder
  operation and C_lib has no `%`; an `fp64` `%` was not written or
  measured.
- `ToInt32`/`ToUint32`: A and B reduce an `int` modulo 2^32. C_lib returns
  0 for non-finite input and otherwise takes `fp64.ToInt(x) % 2^32`. The
  bitwise operators (W4) go from there to `bv32` for `&` and shifts, and
  back through `int` and `fp64.FromReal`.
- `Math.trunc`: C_lib uses `Ceiling` for negative input and `Floor`
  otherwise, so a value in (-1, 0) becomes `-0`. B tracks the sign flag.
- `Math.round`: JavaScript rounds half toward +Infinity, while
  `fp64.Round` rounds ties to even. `Floor(x + 0.5)` is wrong for
  0.49999999999999994 because `x + 0.5` rounds up to 1.0, so C_lib compares
  the distance from `Floor(x)` to `x`. B rounds the exact real with
  `floor(r + 0.5)` and sets the `-0` flag for inputs in [-0.5, -0].
- SameValueZero: in both B and C, `StrictEq(x, y) || (x is NaN && y is
  NaN)`.
- `Math.min`/`Math.max`: explicit NaN and signed-zero cases in B_lib and
  C_lib.

The vectors section checks the rounding, truncation and min/max functions
against fork #23's table (see the topic 5 mapping below): 66 of 66 sampled
vectors verify in B and in C. The `ToInt32` path in C did not verify on
symbolic input (C_bitwise `OrZeroRange` and `OrZeroIdempotent` time out).

### 5. Whether representative LemmaScript proofs are stable under repeated isolated and whole-file verification, not merely whether concrete expressions reduce.

The recorded run gives one isolated run and three seeded whole-file runs
per file, so stability below means agreement among those four runs.

Encoding A: A_lib and A_clamp give the same result in all four runs.
A_safeint verifies whole-file under seeds 1 and 2, times out under seed 3,
and fails one isolated batch with an error. A_bitwise times out in every
run, and under seed 2 one of the timeouts becomes an assertion error. Every
A instability is in a procedure that uses `bv32` or the `SafeInt` sum.

Encoding B: B_lib, B_clamp and B_signedzero give the same result in all
four runs. B_safeint verifies in isolation and under seed 3 and times out
under seeds 1 and 2. B_bitwise verifies whole-file only under seed 3.
B_lerp passes every isolated batch and fails the same hand assertion in
every whole-file run.

Encoding C: every file gives identical counts under all three seeds. The
results are stable in the sense of repeatable; they are repeatable
timeouts. Every C file other than C_lib has at least one timeout in every
run. The procedures that verify are concrete facts or classification
lemmas, while the symbolic range and order properties that the workloads
need (clamp range, midpoint bounds, `| 0` range, safe-integer addition)
time out. Repro R11 isolates the order facts: `Trichotomy` and
`Transitivity` of `fp64.Less`/`LessOrEqual` on non-NaN values time out
under both bundled Z3 versions.

Concrete expressions reduce in B and C: the 66 vector lemmas per encoding
verify, with batch times under 0.2 s each.

Run-to-run variation was observed between full runs of `run.sh` during
development; only the recorded run is committed and cited.

### 6. The minimum Dafny version and any required artifact header/CLI flags.

Encodings A and B use only `int`, `real`, `bv32` and datatypes and verify
on pinned Dafny 4.11.0 with no extra flags beyond `--allow-warnings`,
`--verification-time-limit` and `--library`.

Encoding C needs a Dafny build that contains dafny-lang/dafny#6323 (merged
2025-11-07). The newest tagged release, 4.11.0 (2025-08-25), predates it,
so no tagged release has `fp64`; the spike used the nightly
4.11.1+a869244. No CLI flag was needed to enable `fp64` on the nightly. The
soundness and crash fixes in dafny-lang/dafny#6514 are not in any build:
that PR is an open draft. The literal rounding fix boogie#1141, which
dafny#6514 lists as outside its scope, is not in the Boogie 3.5.5 that the
nightly bundles (repro R08).

The artifact header proposed in DESIGN_NUMBERS.md §6, `// lsc options:
number-semantics=javascript`, was not exercised: the spike's Dafny is
hand-written, not generated by `lsc`. Not measured.

## Mapping to the issue #20 topics

1. Native fp64 coverage vs gaps: §5 answers 1 to 4. Covered:
   classification, IEEE constants, total arithmetic and comparison,
   IEEE equality, exact finite literals, Floor/Ceiling/Round. Gaps: no bit
   patterns (R13), no remainder, `Round` ties to even, compiled `==` and
   the surface operators exclude NaN, no `fp64` in a tagged release, and the
   compiler gaps under "`-t js`" below.
2. Rounding-mode, NaN, `-0` and subnormal fidelity: C follows binary64
   round-to-nearest-even, which is JavaScript's only mode; other rounding
   modes were not measured. NaN and `-0` behave as in JavaScript through the
   static methods and the C_lib wrappers (C_clamp's NaN and `-0` lemmas and
   the vectors verify). The vectors include the subnormal `-5e-324`, whose
   `Math.trunc` and `Math.round` are `-0`, and both B and C verify them. B
   models NaN, the infinities and `-0` but not rounding or overflow (W5
   above). A models none of them.
3. bv64/bv32 ergonomics and solver cost: `bv64` could not be used for
   `fp64` bit patterns (R13), so a `bv64` encoding was not measured. The
   `bv32` round trip through `int` is the slowest part of every encoding:
   A's `Bv32RoundTrip` times out in every run, B's concrete `bv32` examples
   time out in isolation, and C_bitwise fails 12 of its 41 isolated
   batches (11 timeouts) with 349.33 s of summed batch time in
   `results/verify/C_bitwise.csv`. Every encoding converts through `int`
   before reaching `bv32`, so the cost includes that conversion.
4. Z3 timeout behavior: at a 30 s limit, timeouts appear in A_bitwise,
   B_safeint, B_bitwise and every C workload. On the nightly the two
   bundled Z3 versions gave the same repro counts except R12 and R14, where
   they split the failures differently between errors and timeouts. The
   corpus was run with only the default prover of each toolchain; the C
   corpus under z3-4.12.1 was not measured.
5. Shared conformance vector table: feasible for B and C. `vectors/gen-dfy.mjs`
   reads fork #23's `math-special-values.json` (schema
   `lemmascript-math-vectors/1`, sha256 recorded in `versions.txt`) and
   writes one `ObjectIs(Math...(args), expected)` lemma per sampled
   record, with operands as exact decimals from the record's `hex` field.
   It samples every 8th two-argument `Math.min` and `Math.max` record and
   every 2nd `Math.trunc` and `Math.round` record: 17 min, 17 max, 16 trunc
   and 16 round lemmas. B verifies 66 of 66 (100 verified batches including
   well-formedness, 0 errors, 4.20 s); C verifies 66 of 66 (0 errors,
   2.13 s). Encoding A cannot express the NaN, `-0` or fractional values in
   the table. Variadic min/max records and the other Math members in the
   table were not measured.
6. Proof-authoring ergonomics: `@manual` and `@lemma` counts are in the
   table above. B needed the most hand assertions (32), mostly in
   B_safeint and B_lerp, where the datatype must be unfolded into its real
   payload. A needed hand `bv32` facts in A_bitwise. C needs few hints for
   concrete facts but its symbolic lemmas time out with or without the
   hints tried. C also has an authoring hazard that A and B do not: a type
   synonym `type F = fp64` crashes the verifier on the first literal (R10).

## dafny-lang/dafny#6514 repros

dafny#6514 ("feat: sound fp32/fp64 verification, and faithful C#
compilation") is an open draft with no comments; it names four verifier
defects, an ordering incoherence, a loop and division unsoundness, and two
items it does not fix. The spike reproduced each on the nightly, which does
not contain that PR. Columns give verified, errors, time outs, or the exit
code when Dafny produced no summary. Both bundled Z3 versions gave the same
outcome unless noted.

| Repro | What it checks | Result (z3-4.16.0 / z3-4.12.1) | Outcome |
|---|---|---|---|
| P01 | `fp64` on pinned 4.11.0 | resolution error, "Type or type parameter is not declared in this scope: fp64" | `fp64` absent in 4.11.0 |
| R01 | defect 1, `x as int` keeps the result in [-2^63, 2^63) | 6, 2, 0 | Reproduced. `TooSmall` verifies `1e20 as int < 2^63`; `Exact` (`== 10^20`) fails. `fp64.ToInt` is correct: `ToIntExact` verifies, `ToIntTooSmall` fails |
| R02 | defect 2, `fp32.E` 3209 ULP low | 4, 1, 0 | Reproduced. `Buggy` verifies, `Correct` fails |
| R03 | defect 3, `as real` on a newtype over `fp64` skips finiteness | 1, 0, 0 | Reproduced. The false lemma verifies |
| R04a, R04b | defect 4, fp literal without a resolved value (witness-less subset type; assign-such-that) | exit 134 | Reproduced. "Internal error occurred during verification: Exception of type 'Cce+UnreachableException' was thrown" |
| R05 | `<=` versus ghost `==` on signed zeros | 11, 1, 0 | Reproduced. Antisymmetry fails; `SignedZeroWitness` verifies |
| R06a | loop interval inference, `decreases` on an fp local | 4, 1, 0 | Not reproduced in this shape: "decreases expression could not be proved to decrease", which is the correct result |
| R06b | loop interval inference, toggled sign | 6, 0, 0 | Reproduced. `OddCount` verifies a false assertion |
| R07 | `/` by `-0.0` | 5, 3, 0 | Reproduced. `ByNegZero` reports only the invalid-operand error; `ByPosZero` also reports "possible division by zero" |
| R08 | literal `~1e-5` one ULP low (boogie#1141) | 1, 1, 0 | Reproduced. `OneUlpLow` verifies, `CorrectlyRounded` fails |
| R09 | `2.0 as fp64 as int` and `as real` | 2, 0, 4 | Reproduced. `TwoAsInt` and `TwoAsReal` time out at 30 s under both Z3 versions |

R06a and R06b are rewritten from the PR's test `FpUnsoundLoopAndDivision`;
the PR's exact program text was not copied. R04a, R04b and R10 print .NET
stack traces; `results/repro/` keeps the first 40 lines.

The spike added five repros of its own while writing Encoding C:

| Repro | What it checks | z3-4.16.0 | z3-4.12.1 | Outcome |
|---|---|---|---|---|
| R10 | literal assigned to `type F = fp64` | exit 1 | exit 1 | Crash: "System.ArgumentException: Not a float type: F" |
| R11 | trichotomy and transitivity of `fp64.Less`/`LessOrEqual` | 1, 0, 2 | 1, 0, 2 | Both lemmas time out |
| R12 | `FromReal(0.0) == 0.0`, `FromReal(1.0) == 1.0`, `ToInt(-1.0) == -1`, NaN uniqueness | 3, 0, 2 | 3, 1, 1 | Both `FromReal` lemmas fail (timeout or error); the other two verify |
| R13 | `fp64` to and from `bv64` with `as` | exit 2 | exit 2 | Resolution errors quoted under question 1 |
| R14 | `FromReal(0.0)` and `FromReal(1.0)` facts, two false and four true | 1, 4, 1 | 1, 1, 4 | The false `NegZero` and `Pos` claims never verify. Of the true claims, only `IntCast` (`FromReal(0 as real) == 0.0`) verifies; `IsZero`, `NotNegative` and `One` time out or are reported as errors |

R14 shows the verifier reporting errors on true statements
(`NotNegative` and `One` under z3-4.16.0), so an "error" from `FromReal` on
a real literal is not evidence that the statement is false. No R14 lemma
verified a false claim.

## `-t js`

`run.sh` builds each program with `dafny build -t js --no-verify` and runs
the output with Node v24.17.0 (`results/js.csv`, `results/js/`).

| Program | Toolchain | Build | Run | Outcome |
|---|---|---|---|---|
| A_main | pinned | 0 | 0 | Prints 7, 7, 2, 0, 5, 10, the expected values |
| B_main | pinned | 0 | 0 | Prints `NumRaw.NaN`, `NumRaw.Finite(0.0, false)`, `NumRaw.Finite(2.0, false)`, `NumRaw.NaN`, `NumRaw.NegInf`. The values match JavaScript's clamp, negated-guard clamp, lerp, `Infinity + -Infinity` and `1 / -0`; the printed form is the datatype, not a JavaScript number |
| C_main | nightly | 1 | not run | Code generator crash: "Cce+UnreachableException" in `JavaScriptCodeGenerator.TypeName` called from `TypeName_Companion` |
| C_nan | nightly | 1 | not run | The same crash from a single use of `fp64.NaN` |
| C_min | nightly | 0 | 1 | Prints 3.5, 0.3, true; JavaScript prints 3.5, 0.30000000000000004, false. Then throws "TypeError: a.isGreaterThanOrEqualTo is not a function" in `$module.EuclideanDivision` at the division `one / three` |

Node needs `.build/package.json` set to `{ "type": "commonjs" }` to run
any of the outputs, because the checkout's `package.json` declares
`"type": "module"` and Dafny emits CommonJS. `run.sh` writes it.

C_min shows that the nightly's JavaScript backend does not compile `fp64`
as an IEEE double: `0.1 + 0.2` printed 0.3 and compared equal to `0.3`,
and `/` went to the integer division helper. dafny#6514's title names
faithful C# compilation, and its description does not mention JavaScript.

## Not measured

- Encoding C under z3-4.12.1 (the corpus used only z3-4.16.0).
- Any verification time limit other than 30 s, and resource-limit or
  `--isolate-assertions` plus seed combinations.
- A `bv64` bit-pattern encoding, an `fp64` `%`, variadic `Math.min`/`max`,
  and the other Math members in the #23 table.
- Generated Dafny from `lsc` and the §6 artifact header.
- Builds containing dafny#6514.
- `-t js` for the A and B workloads beyond the smoke programs.

## Corrections to the brief

- boogie#1141 merged on 2026-08-20 but is not in Boogie 3.5.5, which both
  toolchains bundle; R08 still reproduces.
- dafny#6514 is an open draft with no comments.
- dafny#6323 merged on 2025-11-07, after the 4.11.0 release.
- The issue body points at #19 for vectors; the brief and this spike use
  fork #23's `math-special-values.json`.
