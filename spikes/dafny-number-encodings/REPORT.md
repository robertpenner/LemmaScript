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

Every number below comes from the run recorded in `results/`, except the
"Run-to-run variance" subsection, which also cites two earlier full runs
kept outside the repository. Anything the spike did not run is marked "not
measured". This report does not recommend an encoding.

## Toolchains and method

`results/versions.txt` is the shared version header for every file in
`results/`; the CSV files carry no version header of their own. From it
(run started 2026-11-19T18:37:55Z on Darwin arm64, 10 logical cpus, Node
v24.17.0):

| | Pinned (A, B) | Nightly (C, repros) |
|---|---|---|
| `dafny --version` | 4.11.0+fcb2042d6d043a2634f0854338c08feeaaaf4ae2 | 4.11.1+a8692441e735a865c378c76e87bcf7d0e6c7c592 (release nightly-2026-11-02-a869244) |
| Boogie (`Boogie.ExecutionEngine` in `DafnyDriver.deps.json`) | 3.5.5 | 3.5.5 |
| Bundled Z3 | z3-4.12.1, z3-4.14.1 | z3-4.12.1, z3-4.16.0 |
| Prover actually used (`verify --boogie -trace`, "Using prover") | z3-4.12.1 | z3-4.16.0 |

The corpus runs use each toolchain's default prover. Each repro runs once
on the nightly per bundled Z3 binary (`run.sh` finds them with a glob of
`z3/bin/z3-*`), selected with `--solver-path`.

The recorded run was, with exit code 0:

```sh
cd spikes/dafny-number-encodings
DAFNY_FP=<nightly>/dafny/dafny ./run.sh
```

`DAFNY` defaults to the `dafny` on PATH (the pinned 4.11.0). In the
recorded run `<nightly>` was the coordinator's scratch download
`.../run-6WMCfLu3/dafny-nightly`. `VECTORS` defaults to the vendored
`vectors/math-special-values.json`, a copy of fork #23's file whose source
commit and sha256 are in `vectors/PROVENANCE.md`. If the vector file is
missing, the vectors section prints a skip and leaves any existing
`results/vectors*` in place. `SECTIONS` selects a subset of `verify repro
js vectors`. `run.sh` checks for the Dafny binaries, Node, perl and the
`bignumber.js` module before it starts, passes relative paths to Dafny, and
removes the checkout's absolute path from the files it writes to
`results/`.

For each corpus file `run.sh` does:

- one isolated run: `dafny verify --allow-warnings
  --verification-time-limit 30 --isolate-assertions --log-format csv;...`
  with `--library corpus/<X>_lib.dfy`. Output in `results/verify/`.
- three whole-file runs, `--boogie -randomSeed:1`, `:2` and `:3`, with the
  same time limit. Output in `results/seeds/`.

`results/summary.csv` holds the verifier's own "N verified, N errors, N time
outs" line for every run, the wall-clock seconds, and three tag counts per
file. Each count matches only a comment tag at the end of a line:

- `// @manual` marks a hand-written hint: an assertion, a ghost variable or
  a call to a helper lemma inside a proof.
- `// @helper` marks a lemma declared only so that another proof can call
  it.
- `// @target` marks a lemma that states a workload property. Workload
  properties written as method or function contracts (W1 and the `bitwise`
  functions) are not tagged.

`@manual` plus `@helper` is the hand-written hint count; `@target` counts
statements of the workload. In isolated runs the verifier counts are per
assertion batch; in whole-file runs they are per Boogie implementation, so
the two are not comparable with each other.

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

Counts are verified, errors, time outs. "s" is wall-clock seconds of the
isolated run. The last three columns are the `@manual`, `@helper` and
`@target` tag counts.

| File | Isolated | s | Seed 1 | Seed 2 | Seed 3 | manual | helper | target |
|---|---|---|---|---|---|---|---|---|
| A_lib | 8, 0, 0 | 1.10 | 5, 0, 0 | 5, 0, 0 | 5, 0, 0 | 0 | 0 | 0 |
| A_safeint | 96, 1, 0 | 15.84 | 7, 0, 0 | 7, 0, 0 | 7, 0, 0 | 3 | 1 | 0 |
| A_clamp | 14, 0, 0 | 1.53 | 6, 0, 0 | 6, 0, 0 | 6, 0, 0 | 0 | 0 | 2 |
| A_bitwise | 73, 0, 3 | 32.00 | 11, 0, 3 | 11, 0, 3 | 11, 0, 3 | 8 | 2 | 4 |
| B_lib | 77, 0, 0 | 6.00 | 16, 0, 0 | 16, 0, 0 | 16, 0, 0 | 0 | 0 | 0 |
| B_safeint | 229, 0, 0 | 11.07 | 18, 0, 0 | 17, 0, 1 | 18, 0, 0 | 15 | 6 | 0 |
| B_clamp | 27, 0, 0 | 1.60 | 8, 0, 0 | 8, 0, 0 | 8, 0, 0 | 0 | 0 | 5 |
| B_signedzero | 46, 0, 0 | 2.45 | 10, 0, 0 | 10, 0, 0 | 10, 0, 0 | 0 | 0 | 8 |
| B_bitwise | 78, 0, 4 | 32.93 | 19, 0, 3 | 18, 1, 3 | 18, 1, 3 | 13 | 2 | 10 |
| B_lerp | 71, 0, 0 | 3.08 | 15, 1, 0 | 15, 1, 0 | 15, 1, 0 | 12 | 3 | 6 |
| C_lib | 5, 0, 0 | 1.66 | 3, 0, 0 | 3, 0, 0 | 3, 0, 0 | 0 | 0 | 0 |
| C_safeint | 86, 0, 33 | 230.31 | 4, 1, 2 | 4, 0, 3 | 4, 0, 3 | 3 | 0 | 0 |
| C_clamp | 8, 0, 4 | 32.11 | 2, 0, 3 | 2, 0, 3 | 2, 0, 3 | 0 | 0 | 5 |
| C_signedzero | 21, 0, 1 | 31.96 | 7, 0, 1 | 7, 0, 1 | 7, 0, 1 | 0 | 0 | 8 |
| C_bitwise | 61, 5, 12 | 102.63 | 10, 2, 9 | 10, 2, 9 | 10, 2, 9 | 11 | 2 | 10 |
| C_lerp | 19, 2, 8 | 62.60 | 6, 0, 5 | 6, 0, 5 | 6, 0, 5 | 0 | 0 | 6 |

Totals across each encoding's files, from the isolated rows of
`results/summary.csv`:

| Encoding | `@manual` | `@helper` | hand-written hints (`@manual` + `@helper`) | `@target` |
|---|---|---|---|---|
| A | 11 | 3 | 14 | 6 |
| B | 40 | 11 | 51 | 29 |
| C | 14 | 2 | 16 | 29 |

The target counts differ mainly because of W3, W4 and W5. Encoding A has
no W3 or W5 file. In W4, `A_bitwise.dfy` states its concrete checks
(`OrZero(2147483648) == -2147483648`, `Ushr0(-1) == 4294967295`, the two
`Imul` cases, `And(-1, 255) == 255` and `UshrN(-1, 28) == 15`) as
assertions in one untagged `method Examples()`, while B and C split the
same checks into the four target lemmas `ImulExamples`, `Ushr0Examples`,
`AndExample` and `UshrExample`. The three `@manual` assertions inside
`Examples` are counted as hints. A also has no `OrZeroSpecials` or
`OrZeroRange` lemma; see "Non-equivalent obligations" below.

The hint counts measure what the author wrote, not how much effort each
encoding would need to verify fully. The C files keep the A-equivalent
hints (`MulBound`, `Bv32RoundTrip`, the two
`ToInt32` assertions in `ImulSmall`, the two sequence assertions in
`SumBounded`) whether or not the proof then verified.

Where the failures are, from `results/verify/*.csv` (isolated batches that
did not pass, per procedure) and the `Error` lines in `results/verify/*.out`
and `results/seeds/*.out`:

- A_safeint, isolated: one error, `result of operation might violate
  newtype constraint for 'SafeInt'` at `s := s + a[i]` (75,11) in
  `SumBounded` (41 of 42 batches pass). The procedure verifies in all three
  seeded whole-file runs.
- A_bitwise: the helper `Bv32RoundTrip`, `(x as bv32) as int == x` for
  `0 <= x < 2^32`, times out in every run. In the isolated run `Examples`
  times out at `assert And(-1, 255) == 255` (90,2) and `assert UshrN(-1,
  28) == 15` (92,2), the two concrete assertions that go through `bv32`.
  Whole-file, `AndWithSelf`, `Bv32RoundTrip` and `Examples` time out under
  every seed.
- B_safeint: every isolated batch passes (229 of 229). Whole-file,
  `Midpoint` timed out under seed 2 in this run; see "Run-to-run variance".
- B_bitwise, isolated: `AndExample` (67,37), `UshrExample` (72,31),
  `AndWithSelf` (105,20) and `Bv32RoundTrip` each time out in one batch.
  Whole-file, `AndExample`, `AndWithSelf` and `Bv32RoundTrip` time out
  under every seed, and seeds 2 and 3 report that `ImulSmall`'s
  postcondition `Imul(a, b).r == a.r * b.r` (90,45) could not be proved;
  under seed 1 and in isolation it verifies.
- B_lerp: every isolated batch passes (71 of 71). Every whole-file run
  reports `assertion might not hold` at `assert 0.0 <= m.r <= d.r` (49,20),
  a hand assertion inside `LerpInRange`.
- C_safeint, isolated: `Midpoint` well-formedness passes 0 of 6 batches,
  `BinarySearch` 36 of 57 and `SumBounded` 43 of 49; all 33 failures are
  timeouts. Whole-file, `Midpoint` and `BinarySearch` time out under every
  seed. `SumBounded` times out under seeds 2 and 3; under seed 1 the
  invariant `(s as real) <= (i as real) * (bound as real)` (73,26) is
  reported as not maintained.
- C_clamp: `ClampInRange` (2 of 3 batches fail), `ClampNegInRange` (1 of
  3) and `GuardsAgreeOffNaN` (1 of 1) time out. The concrete NaN and `-0` facts
  about clamp verify.
- C_signedzero: `NormKeyCollapses`, that SameValueZero equals `Object.is`
  after mapping `-0` to `+0`, times out. `ObjectIsIsIdentity` (now stated
  as `ObjectIs(x, y) <==> x == y`) and the other signed-zero lemmas verify.
- C_bitwise, isolated: 17 of 78 batches fail, in `OrZeroSpecials` (3 of 5
  batches fail), `OrZeroRange` (2 of 5), `OrZeroIdempotent`, `ImulExamples` (both
  batches), `Ushr0Examples`, `AndExample`, `UshrExample`, `OrZeroOnInt32`
  (1 of 5), `ImulSmall` (3 of 21), `AndWithSelf` and `Bv32RoundTrip`.
  Twelve are timeouts. The five errors are `ensures OrZero(fp64.NaN) ==
  0.0` (36,27), `ensures Imul(-1.0, 8.0) == -8.0` (56,33), `OrZeroOnInt32`'s
  `ensures OrZero(x) == x` (86,20), and `ImulSmall`'s `assert ToInt32(a) ==
  (a as real).Floor` (95,2) and `assert ToInt32(b) == (b as real).Floor`
  (96,2). All five statements are true by the definitions in `C_lib.dfy`
  and `C_bitwise.dfy` (`ToInt32` of a non-finite value is 0, `ToInt32` of
  a finite value is `fp64.ToInt(x)` reduced modulo 2^32, and `OrZero(x)` is
  `fp64.FromReal(ToInt32(x) as real)`), so each one is an incomplete proof.
  For `OrZero(NaN)`, the right-hand side reduces to `fp64.FromReal(0 as
  real) == 0.0`, which repro R14 `IntCast` proves on its own. Whole-file,
  the seven lemmas from `OrZeroSpecials` to `UshrExample`, `AndWithSelf`
  and `Bv32RoundTrip` time out under every seed, and `OrZeroOnInt32`'s
  postcondition and `ImulSmall`'s assertion at (96,2) are errors.
- C_lerp: `LerpExtremesIsNaN` verifies (Encoding C proves that
  `lerp(-MAX_VALUE, MAX_VALUE, 0)` is NaN). In isolation,
  `LerpAtOneOvershoots` (1 of 2 batches fail), `LerpEndpointsSmallInts` (2
  of 4), `LerpInRangeSmallInts` (3 of 5, the postcondition goals at
  (53,24), (54,26) and (54,64)), `BridgeRoundTrip` (2 of 3) and `BridgeAdd`
  (2 of 9) fail. The two errors are `BridgeRoundTrip`'s `fp64.ToInt(fp64.FromReal(i
  as real)) == i` (67,35) and `BridgeAdd`'s `Add(x, y) as real == x as real
  + y as real` (75,50), both true statements about IEEE binary64 for safe
  integers. Whole-file, all five of these lemmas time out under every seed.

### Non-equivalent obligations

The workloads were aligned across encodings where the encoding can state
the same property. These obligations still differ:

- W1 `SumBounded`: B requires every element to be `IsIntNum` and not
  `-0`; A has no `-0` and C requires `IsSafeIntF`, which admits `-0` but
  bounds the elements below by `fp64.LessOrEqual(0.0, a[i])`. B and C state
  the sum against a `real`-valued `SumR`, A against an `int`-valued `Sum`.
- W1 `BinarySearch`: A requires `|a| < 2^32` and returns a `SafeInt`; B
  has no length bound and returns an `int`; C requires `|a| < 2^32` and
  returns an `int`. B and C state hits and misses with `StrictEq`, A with
  `==` and `!in`.
- W2: A states `GuardFormsAgree` and `ClampIsMinMax` for all `SafeInt`
  arguments. B and C state `NaNSeparatesGuards`, `ClampInRange`,
  `ClampNegInRange`, `GuardsAgreeOffNaN` and `ClampKeepsNegZero`, which
  have no A counterpart, and neither B nor C states `ClampIsMinMax`.
- W3: B has `RemSign` (the sign of `%` results), which C lacks. C has
  `ObjectIsIsIdentity` (the compiled `ObjectIs` agrees with ghost `==`),
  which B lacks because B's `==` is datatype equality.
- W4: A states its concrete checks in the untagged `method Examples()`;
  B and C use four target lemmas. `OrZeroSpecials` (NaN and the
  infinities map to 0) and `OrZeroRange` (the result of `x | 0` lies in
  the int32 range) exist only in B and C, because A has no non-finite or
  non-integer values. `OrZeroOnInt32` excludes `-0` in B and C, since
  `-0 | 0` is `+0`; A has no `-0`.
- W5: B states `LerpInRange` for all finite `a <= b` and `t` in
  `[0, 1]` and `LerpAtOne` (`lerp(a, b, 1) == b`), which are true for exact
  reals. C states `LerpAtOneOvershoots` and `LerpExtremesIsNaN`, the
  JavaScript counterexamples to `LerpAtOne` and `LerpExtremesInB`. C's
  `LerpEndpointsSmallInts` and `LerpInRangeSmallInts` restrict `a` and `b`
  to integers in `[-1024, 1024]`; `t` is symbolic in
  `LerpInRangeSmallInts`.
- W5 bridges: B's `BridgeRoundTrip`, `BridgeAdd` and `BridgeMul` are
  stated for every `int`, with the preconditions `i + j != 0` for
  `BridgeAdd` and `i != 0 && j != 0` for `BridgeMul`. C's
  `BridgeRoundTrip` and `BridgeAdd` are restricted to safe integers, where
  binary64 is exact, and C has no `BridgeMul`.

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
obligations, and the nightly does not check them consistently. In repro
R07 both methods divide a finite nonzero `x` by a zero literal, so the
invalid-operand check (0/0) cannot fire and only the zero-divisor check
applies. `ByPosZero` (`x / 0.0`) reports "possible division by zero" at
(19,9). `ByNegZero` (`x / -0.0`) verifies with no error, so the checked `/`
accepts a `-0.0` divisor that it rejects as `+0.0`.
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
`ObjectIs` in C_lib agrees with it (`ensures ObjectIs(x, y) <==> x ==
y`; it verifies in the isolated run and under all three seeds). Compiled `==` requires both operands to
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
symbolic input (C_bitwise `OrZeroRange` and `OrZeroIdempotent` time out,
and `OrZeroOnInt32` reports an error on a true postcondition).

### 5. Whether representative LemmaScript proofs are stable under repeated isolated and whole-file verification, not merely whether concrete expressions reduce.

The recorded run gives one isolated run and three seeded whole-file runs
per file, so stability below means agreement among those four runs.
Agreement within one run does not establish that a result is fixed: the
"Run-to-run variance" subsection below lists the rows whose counts changed
between three full runs, and every one of them involves a goal that sits
near the 30 s limit.

Encoding A: A_lib and A_clamp give the same result in all four runs.
A_safeint verifies whole-file under all three seeds in this run and fails
one isolated batch with a newtype error; an earlier full run timed out or
failed under seed 3. A_bitwise has three timeouts in every run here; in an
earlier run one of them became an assertion error under seed 2. Every
unstable A row involves `bv32` or the `SafeInt` sum.

Encoding B: B_lib, B_clamp and B_signedzero give the same result in all
four runs. B_safeint verifies in isolation; whole-file, `Midpoint` timed out
under seed 2 in this run. In the two runs of the 8ac8174 version of the
file, it timed out under seeds 1 and 2 in one run and under no seed in the
other. B_bitwise has three or four timeouts in every run, and
`ImulSmall` verifies under some seeds and fails under others. B_lerp
passes every isolated batch and fails the same hand assertion in every
whole-file run.

Encoding C: every file gives identical whole-file counts under all three
seeds except C_safeint, where `SumBounded` times out under two seeds and
reports an invariant error under the third. Those results repeat because
most of them are timeouts. Every C file other than C_lib has at least one
timeout in every run. The procedures that verify are concrete facts or
classification lemmas, while the symbolic range and order properties that
the workloads need (clamp range, midpoint bounds, `| 0` range, safe-integer
addition, lerp range) time out or report errors on true statements. Repro
R11 isolates the order facts: `Trichotomy` and `Transitivity` of
`fp64.Less`/`LessOrEqual` on non-NaN values time out under both bundled Z3
versions.

Concrete expressions reduce in B and C: the 66 vector lemmas per encoding
verify, and no single vector batch took more than 0.08 s
(`results/vectors/*_vectors.csv`).

#### Run-to-run variance

Three full runs of `run.sh` produced the counts below. "Worker" is the run
committed at 8ac8174, "Rerun" is the coordinator's rerun of 8ac8174 on the
same machine and toolchains, and "Current" is the run committed with this
report. The worker and rerun outputs are not in the repository (they are in
the coordinator's scratch directory, `verify-20/results-worker/` and
`verify-20/results-rerun/`). Counts are verified, errors, time outs. Every
other exit code, `js.csv`, `vectors.csv` and repro classification matched
across the three runs.

Rows whose source file did not change in a way that affects verification
between the runs:

| Row | Worker | Rerun | Current |
|---|---|---|---|
| A_bitwise seed 2 | 11, 1, 2 | 11, 0, 3 | 11, 0, 3 |
| R12 on Z3 4.12.1 | 3, 1, 1 | 3, 0, 2 | 3, 1, 1 |
| R12 on Z3 4.16.0 | 3, 0, 2 | 3, 0, 2 | 3, 2, 0 |
| R14 on Z3 4.12.1 | 1, 1, 4 | 1, 1, 4 | 1, 3, 2 |

Rows that differed between the worker run and the rerun of the same
source; the file then changed before the current run, so the current
column is listed for reference and is not a third sample of the same
proof:

| Row | Worker | Rerun | Current |
|---|---|---|---|
| A_safeint seed 3 | 6, 0, 1 | 6, 1, 0 | 7, 0, 0 |
| B_safeint seed 1 | 17, 0, 1 | 18, 0, 0 | 18, 0, 0 |
| B_safeint seed 2 | 17, 0, 1 | 18, 0, 0 | 17, 0, 1 |
| C_bitwise isolated | 29, 1, 11 | 29, 2, 10 | 61, 5, 12 |

These rows are unstable near the time limit: the same goal times out in
one run and verifies, or is reported as an error, in another. A count in
any of these rows describes one run only. The workload changes between
8ac8174 and the current run (see "Non-equivalent obligations") also changed
the counts of A_safeint isolated, B_safeint isolated, B_bitwise, C_safeint,
C_bitwise, C_lerp and repro R07; those differences come from the code and
are not counted as variance. C_signedzero changed (`ObjectIsIsIdentity`
now uses `==`) and kept the same counts.

### 6. The minimum Dafny version and any required artifact header/CLI flags.

Encodings A and B use only `int`, `real`, `bv32` and datatypes and run
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
   (`AndExample` and `UshrExample`) time out in isolation, and C_bitwise
   fails 17 of its 78 isolated batches (5 errors, 12 timeouts) with
   454.61 s of summed batch time in `results/verify/C_bitwise.csv`. Every encoding converts through `int`
   before reaching `bv32`, so the cost includes that conversion.
4. Z3 timeout behavior: at a 30 s limit, timeouts appear in A_bitwise,
   B_safeint, B_bitwise and every C workload. In the recorded run the two
   bundled Z3 versions on the nightly gave the same repro counts except R12
   and R14, where they split the failures differently between errors and
   timeouts. Those two repros also changed counts between full runs under
   the same Z3 version (see "Run-to-run variance"). The
   corpus was run with only the default prover of each toolchain; the C
   corpus under z3-4.12.1 was not measured.
5. Shared conformance vector table: feasible for B and C. `vectors/gen-dfy.mjs`
   reads the vendored copy of fork #23's `math-special-values.json`
   (`vectors/math-special-values.json`, schema `lemmascript-math-vectors/1`,
   provenance and sha256 in `vectors/PROVENANCE.md` and
   `results/versions.txt`) and
   writes one `ObjectIs(Math...(args), expected)` lemma per sampled
   record, with operands as exact decimals from the record's `hex` field.
   It samples every 8th two-argument `Math.min` and `Math.max` record and
   every 2nd `Math.trunc` and `Math.round` record: 17 min, 17 max, 16 trunc
   and 16 round lemmas. B verifies 66 of 66 (100 verified batches including
   well-formedness, 0 errors, 2.56 s wall time); C verifies 66 of 66 (0
   errors, 2.90 s wall time). Encoding A cannot express the NaN, `-0` or fractional values in
   the table. Variadic min/max records and the other Math members in the
   table were not measured.
6. Proof-authoring ergonomics: `@manual`, `@helper` and `@target` counts
   are in the tables above. B needed the most hand assertions (40): 15 in
   B_safeint, 13 in B_bitwise and 12 in B_lerp, where the datatype must be
   unfolded into its real payload. A needed 8 hand `bv32` facts in
   A_bitwise. C needs few hints for
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
| R07 | `/` by `-0.0`, finite nonzero dividend | 7, 1, 0 | Reproduced. `ByPosZero` reports "possible division by zero" at (19,9); `ByNegZero` verifies |
| R08 | literal `~1e-5` one ULP low (boogie#1141) | 1, 1, 0 | Reproduced. `OneUlpLow` verifies, `CorrectlyRounded` fails |
| R09 | `2.0 as fp64 as int` and `as real` | 2, 0, 4 | Reproduced. `TwoAsInt` and `TwoAsReal` time out at 30 s under both Z3 versions |

R06a, R06b and R07 are rewritten from the PR's test
`FpUnsoundLoopAndDivision`; the PR's exact program text was not copied.
`results/repro/` keeps every output that contains the "Dafny program
verifier finished" summary line in full. Only outputs without that line
are cut to their first 40 lines: the .NET stack traces of R04a, R04b and
R10, and the short resolution errors of P01 and R13, which are shorter
than 40 lines.

The spike added five repros of its own while writing Encoding C:

| Repro | What it checks | z3-4.16.0 | z3-4.12.1 | Outcome |
|---|---|---|---|---|
| R10 | literal assigned to `type F = fp64` | exit 1 | exit 1 | Crash: "System.ArgumentException: Not a float type: F" |
| R11 | trichotomy and transitivity of `fp64.Less`/`LessOrEqual`, and that a value between `0.0` and a finite bound is finite | 1, 0, 2 | 1, 0, 2 | `Trichotomy` and `Transitivity` time out; `NotGreaterThanFiniteIsFinite` verifies |
| R12 | `FromReal(0.0) == 0.0`, `FromReal(1.0) == 1.0`, `ToInt(-1.0) == -1`, NaN uniqueness | 3, 2, 0 | 3, 1, 1 | Both `FromReal` lemmas fail: under z3-4.16.0 both are errors, under z3-4.12.1 `FromRealZero` times out and `FromRealOne` is an error. `ToIntNegOne` and `NaNIsUnique` verify. The split between errors and timeouts changed between full runs |
| R13 | `fp64` to and from `bv64` with `as` | exit 2 | exit 2 | Resolution errors quoted under question 1 |
| R14 | `FromReal(0.0)` and `FromReal(1.0)` facts, two false and four true | 1, 4, 1 | 1, 3, 2 | The false `NegZero` and `Pos` claims never verify. Of the true claims, only `IntCast` (`FromReal(0 as real) == 0.0`) verifies. Under z3-4.16.0 `NotNegative` and `One` are errors and `IsZero` times out; under z3-4.12.1 `One` is an error and `IsZero` and `NotNegative` time out. The split changed between full runs |

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

The brief for this issue already corrected the issue body on these points,
and the spike confirmed them:

- boogie#1141 merged on 2026-08-20.
- dafny#6514 is an open draft. It also has no comments.
- dafny#6323 merged on 2025-11-07, after the 4.11.0 release.
- The issue body points at #19 for vectors; the brief and this spike use
  fork #23's `math-special-values.json`.

The spike found one more point that neither the issue body nor the brief
states: boogie#1141 is not in Boogie 3.5.5, the version both toolchains
bundle, so the literal rounding defect it fixes still reproduces on the
nightly (R08).
