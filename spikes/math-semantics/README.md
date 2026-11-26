# JavaScript `Math` semantics table and special-value vectors

Spike for [robertpenner/LemmaScript#23](https://github.com/robertpenner/LemmaScript/issues/23).
It writes down what each JavaScript `Math` member that LemmaScript lowers, or
plans to lower, means according to ECMAScript, and compares that meaning with
the functions the backends offer today. It feeds #19 (vector ingestion), #20
and #22 (binary64 spikes), and #21 (the Lean idealized-real prototype). It
supplies evidence for `DESIGN_NUMBERS.md` §9 Question 7 and does not choose an
answer.

Contents of this directory:

- `README.md`: this file, including the normative table.
- `vectors/gen.mjs` and `vectors/math-special-values.json`: special-value
  vectors produced by Node.
- `lean/Divergences.lean`: compiling Lean `example`s and `#check`s for every
  Mathlib declaration cited below, and `#eval`s of Lean `Float` behaviour.
- `fixtures/*.ts` and `fixtures/run-dafny-gen.mjs`: one small TypeScript
  function per member and backend type, used to record what
  `lsc gen --backend=dafny` emits.

## Sources and versions

| Item                 | Version                                                                                                                                              |
| -------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------- |
| ECMAScript text      | ECMAScript 2026 Language Specification, fetched 2026-11-19 from <https://tc39.es/ecma262/2026/multipage/> (`numbers-and-dates.html`, `ecmascript-data-types-and-values.html`, `overview.html`, `notational-conventions.html`) |
| Node                 | v24.17.0 (V8 13.6.233.17-node.49)                                                                                                                    |
| Lean                 | 4.34.0 (`lean-toolchain` of this repository)                                                                                                         |
| Mathlib              | v4.34.0 (`lake-manifest.json` of this repository)                                                                                                    |
| Dafny                | 4.11.0                                                                                                                                               |
| LemmaScript checkout | `60cab87` (fork `main` at the start of the spike)                                                                                                    |

Every quotation in this file is copied from the fetched specification text.
Superscripts that the HTML renders with `<sup>` are written the same way here.

### Definitions the table relies on

4.4.1, implementation-approximated (`sec-implementation-approximated`):

> An implementation-approximated facility is one that defers its definition to
> an external source while recommending an ideal behaviour. ... Some
> mathematical operations, such as Math.exp, are implementation-approximated.

21.3.2, Function Properties of the Math Object, Note:

> The behaviour of the functions acos, acosh, asin, asinh, atan, atanh, atan2,
> cbrt, cos, cosh, exp, expm1, hypot, log, log1p, log2, log10, pow, random, sin,
> sinh, tan, and tanh is not precisely specified here except to require specific
> results for certain argument values that represent boundary cases of
> interest.

The same Note says "it is recommended (but not specified by this standard) that
implementations use the approximation algorithms for IEEE 754-2019 arithmetic
contained in fdlibm".

5.2.5 defines 𝔽:

> A conversion from a mathematical value or extended mathematical value x to a
> Number is denoted as "the Number value for x" or 𝔽(x), and is defined in
> 6.1.6.1.

6.1.6.1 gives that conversion: "Choose the member of this set that is closest
in value to x. If two values of the set are equally close, then the one with an
even significand is chosen". A step of the form "Return 𝔽(...)" therefore fixes
one Number value (round to nearest, ties to even), and the table classifies it
as exact.

### How to read the table

- **Finite results** says whether the step that computes the result for an
  ordinary finite argument fixes one Number value (**exact**) or returns "an
  implementation-approximated Number value" (**approximated**). The quoted
  sentence is that step.
- **Exact special cases** lists the steps that return a fixed value for NaN,
  ±0, ±∞, or other boundary arguments. Special cases the specification itself
  states as approximated (for example `Math.atan(+∞)`) are marked as such.
- **Real meaning agrees on** gives the inputs where the mathematical function
  named by the specification is defined on the reals and the specification
  intends that value (before rounding). Inputs outside it are NaN, ±∞, -0, or
  points where the specification returns a special value.
- **Mathlib** names the Mathlib declaration closest to the member. Mathlib's
  `ℝ` has no NaN, no ±∞, and no -0, so those JavaScript inputs and results have
  no Mathlib counterpart in any row; the column lists only the additional finite
  real inputs where Mathlib's value differs from JavaScript. Every declaration
  named here is checked with `#check` in `lean/Divergences.lean`, and every
  divergence also has a compiling `example` there unless the row says
  otherwise.
- **Lean `Float`** names the declaration in Lean 4.34.0 `Init/Data/Float/` and
  whether it is a `def` with a `Float.Model` body (**model-backed**, so the
  kernel can reason about it) or an `opaque` declaration whose only meaning is
  the C function named in `@[extern]` (**opaque**). Both kinds compile to the C
  function. See [Lean `Float` inventory](#lean-float-inventory).
- **Dafny at `60cab87`** reports what `lsc gen --backend=dafny` emitted for the
  fixtures in `fixtures/`. "Rejected" means `lsc gen` exited 1 with
  `ERROR: Dafny emission failed for 'f' in <file>: Unsupported Dafny method call: .<name>() on unknown`.
  For emitted files the column quotes the count line from `dafny verify`.
  Most fixtures have no `requires` or `ensures`, so Dafny reports
  "0 verified, 0 errors": it parsed and typechecked the file and had no proof
  obligation to discharge. Only a fixture with a contract or a subtype result
  (such as `nat`) produces a nonzero "verified" count. See
  [Dafny status](#dafny-status).

## Normative table

| Member | ECMAScript 2026 clause | Finite results, with the deciding sentence | Exact special cases | Real meaning agrees on | Mathlib counterpart and divergences | Lean `Float` (4.34.0) | Dafny at `60cab87` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Math.abs` | 21.3.2.1 `sec-math.abs` | Exact: "If n < -0𝔽, return -n." then "Return n." | NaN → NaN; -0 → +0; +∞ → +∞; -∞ → +∞ | all finite n | `abs` on `ℝ`; no finite divergence | `Float.abs`, model-backed `def` (Float.lean:524, extern `fabs`) | int: `MathAbs(x)`, whose preamble returns `nat`; Dafny proves that subtype obligation ("1 verified, 0 errors"). real: `MathAbsReal(x)`; "0 verified, 0 errors" (parsed and typechecked only) |
| `Math.min` | 21.3.2.26 `sec-math.min` | Exact: "If number < lowest, set lowest to number." Note: "+0𝔽 is considered to be larger than -0𝔽." | any NaN argument → NaN; min(+0, -0) → -0; no arguments → +∞ | all finite arguments | `min` on `ℝ`; no finite divergence | `instance : Min Float := minOfLe` (Float.lean:529) over model-backed `Float.decLe`; NaN and ±0 results depend on argument order ([table below](#lean-float-against-node)) | int: `MathMin(a, b)`; real: `MathMinReal(a, b)`; both "0 verified, 0 errors" (parsed and typechecked only); no NaN or -0 case. Positional calls lower only with exactly two arguments (`transform.ts` checks `e.args.length === 2`); `Math.min(x, y, z)` is rejected. Spread `Math.min(...xs)` lowers to `MinOfSeq(xs)`, which has `requires \|s\| > 0`; JavaScript returns +∞ for an empty array, and Dafny reports the unguarded call as "function precondition could not be proved" |
| `Math.max` | 21.3.2.25 `sec-math.max` | Exact: "If number > highest, set highest to number." Same Note as `min`. | any NaN argument → NaN; max(-0, +0) → +0; no arguments → -∞ | all finite arguments | `max` on `ℝ`; no finite divergence | `instance : Max Float := maxOfLe` (Float.lean:531); NaN and ±0 results depend on argument order | int: `MathMax(a, b)`; real: `MathMaxReal(a, b)`; both "0 verified, 0 errors" (parsed and typechecked only); no NaN or -0 case. Same arity rule as `min`. Spread `Math.max(...xs)` lowers to `MaxOfSeq(xs)` with `requires \|s\| > 0`; JavaScript returns -∞ for an empty array |
| `Math.floor` | 21.3.2.16 `sec-math.floor` | Exact: "Return the greatest (closest to +∞) integral Number value that is not greater than n." | NaN, ±∞, ±0 → n; 0 < n < 1 → +0 | all finite n | `Int.floor` (`⌊x⌋`); no finite divergence | `Float.floor`, opaque (Float.lean:510, extern `floor`) | int: identity; real: `FloorReal(x)` = `x.Floor` (result `int`); both "0 verified, 0 errors" (parsed and typechecked only). `Math.floor(a / b)` with integral `a` and `b` lowers to `JSFloorDiv(a, b)`, which has `requires b != 0`; JavaScript gives ±∞ or NaN when b is 0, and the exact integer quotient can differ from `Math.floor` of the rounded binary64 quotient outside the safe-integer range (`Math.floor(2 ** 60 / 3)` is 384307168202282304, the integer floor is 384307168202282325) |
| `Math.ceil` | 21.3.2.10 `sec-math.ceil` | Exact: "Return the smallest (closest to -∞) integral Number value that is not less than n." | NaN, ±∞, ±0 → n; -1 < n < 0 → -0 | all finite n | `Int.ceil` (`⌈x⌉`); no finite divergence | `Float.ceil`, opaque (Float.lean:498, extern `ceil`) | int: identity; real: `CeilReal(x)` (result `int`); both "0 verified, 0 errors" (parsed and typechecked only) |
| `Math.round` | 21.3.2.29 `sec-math.round` | Exact: "Return the integral Number closest to n, preferring the Number closer to +∞ in the case of a tie." | NaN, ±∞, integral n → n; 0 < n < 0.5 → +0; -0.5 ≤ n < 0 → -0 | all finite n | `round` with `round_eq` (`round x = ⌊x + 1/2⌋`): ties go toward +∞ as in JavaScript; `example` checks round(-2.5) = -2, round(2.5) = 3, round(-0.5) = 0 (JavaScript gives -0, which `ℝ` cannot express) | `Float.round`, opaque (Float.lean:517, extern C `round`, ties away from zero): `Float.round (-2.5)` is -3 and `Float.round (-0.5)` is -1, JavaScript gives -2 and -0 | rejected (int and real) |
| `Math.trunc` | 21.3.2.37 `sec-math.trunc` | Exact: "Return the integral Number nearest n in the direction of +0𝔽." | NaN, ±∞, ±0 → n; 0 < n < 1 → +0; -1 < n < 0 → -0 | all finite n | No declaration cited. It can be written with `Int.floor` for x ≥ 0 and `Int.ceil` for x < 0. Unverified: whether Mathlib has a dedicated truncation for `ℝ`; I did not search all of Mathlib. | absent (no `Float.trunc` in the 4.34.0 sources) | rejected (int and real) |
| `Math.sign` | 21.3.2.30 `sec-math.sign` | Exact: "If n < -0𝔽, return -1𝔽." then "Return 1𝔽." | NaN, +0, -0 → n; +∞ → 1; -∞ → -1 | all finite n | `Real.sign`; `Real.sign_zero` gives 0 at 0, matching +0; no finite divergence | absent (no `Float.sign`) | rejected (int and real) |
| `Math.sqrt` | 21.3.2.33 `sec-math.sqrt` | Exact: "Return 𝔽(the square root of ℝ(n))." | NaN, +0, -0, +∞ → n; n < -0 → NaN | n ≥ 0 | `Real.sqrt`. Diverges for x < 0: `Real.sqrt_eq_zero_of_nonpos` gives 0 where JavaScript gives NaN; `example` checks √(-1) = 0 | `Float.sqrt`, model-backed `def` (Float.lean:478, extern `sqrt`) | rejected |
| `Math.cbrt` | 21.3.2.9 `sec-math.cbrt` | Approximated: "Return an implementation-approximated Number value representing the cube root of ℝ(n)." | NaN, ±∞, ±0 → n | all finite n | No cube-root declaration cited (unverified whether one exists). Writing it as `x ^ (1/3 : ℝ)` with `Real.rpow` diverges for x < 0: `example` checks (-8) ^ (1/3) = 1, where `Math.cbrt(-8)` is -2 | `Float.cbrt`, opaque (Float.lean:486, extern `cbrt`) | rejected |
| `Math.pow` and `**` | 21.3.2.27 `sec-math.pow` ("Return Number::exponentiate(base, exponent).") and 6.1.6.1.3 `sec-numeric-types-number-exponentiate` | Approximated: "It returns an implementation-approximated value representing the result of raising base to the exponent power." The last step: "Return an implementation-approximated Number value representing the result of raising ℝ(base) to the ℝ(exponent) power." | exponent NaN → NaN; exponent ±0 → 1 (even for base NaN); base NaN → NaN; base +∞ → +∞ if exponent > 0, else +0; base -∞ → -∞ if exponent > 0 and an odd integral Number, +∞ if exponent > 0 otherwise, -0 if exponent < 0 and an odd integral Number, +0 if exponent < 0 otherwise; base +0 → +0 if exponent > 0, else +∞; base -0 → -0 if exponent > 0 and an odd integral Number, +0 if exponent > 0 otherwise, -∞ if exponent < 0 and an odd integral Number, +∞ if exponent < 0 otherwise (only base -∞ and base -0 depend on the exponent being an odd integral Number); exponent +∞ with abs(base) > 1, = 1, < 1 → +∞, NaN, +0; exponent -∞ with abs(base) > 1, = 1, < 1 → +0, NaN, +∞; base < -0 with non-integral exponent → NaN | base > 0 with finite exponent; base < 0 with integral exponent; base = 0 with exponent ≥ 0 (0 ** 0 is 1, the same value as the real convention and `Real.rpow_zero`) | `Real.rpow`. Diverges at base 0 with exponent < 0: `Real.zero_rpow` gives 0 where JavaScript gives +∞ (`example`: 0 ^ (-1) = 0). Diverges at base < 0 with non-integral exponent: `Real.rpow_def_of_neg` defines a finite value where JavaScript gives NaN (`example`s: (-1) ^ (1/2) = 0 and (-8) ^ (1/3) = 1). Agrees: `Real.rpow_zero`, `Real.one_rpow`, `Real.rpow_natCast` (`example`: (-2) ^ 3 = -8) | `Float.pow`, opaque (Float.lean:471, extern C `pow`); `^` is `instance : HomogeneousPow Float := ⟨Float.pow⟩` (Float.lean:527). C `pow` returns 1 for 1 ^ NaN and (±1) ^ (±∞); JavaScript returns NaN | `Math.pow`: rejected. `x ** y`: `lsc gen` exits 0 and emits `(x ** y)`, which Dafny 4.11 rejects with `Error: invalid UnaryExpression` (parse error) |
| `Math.exp` | 21.3.2.14 `sec-math.exp` | Approximated: "Return an implementation-approximated Number value representing the exponential function of ℝ(n)." | NaN, +∞ → n; ±0 → 1; -∞ → +0 | all finite n | `Real.exp`; no finite divergence | `Float.exp`, opaque (Float.lean:436, extern `exp`) | rejected |
| `Math.expm1` | 21.3.2.15 `sec-math.expm1` | Approximated: "Return an implementation-approximated Number value representing exp - 1." | NaN, ±0, +∞ → n; -∞ → -1 | all finite n | No `expm1` declaration cited; `Real.exp x - 1` has no finite divergence | absent (no `Float.expm1`) | rejected |
| `Math.log` | 21.3.2.21 `sec-math.log` | Approximated: "Return an implementation-approximated Number value representing ln(ℝ(n))." | NaN, +∞ → n; 1 → +0; ±0 → -∞; n < -0 → NaN | n > 0 | `Real.log`. Diverges at 0: `Real.log_zero` gives 0 where JavaScript gives -∞. Diverges for x < 0: `Real.log_neg_eq_log` gives log(-x) = log x where JavaScript gives NaN (`example`: log(-1) = 0) | `Float.log`, opaque (Float.lean:450, extern `log`) | rejected |
| `Math.log1p` | 21.3.2.22 `sec-math.log1p` | Approximated: "Return an implementation-approximated Number value representing ln(1 + ℝ(n))." | NaN, ±0, +∞ → n; -1 → -∞; n < -1 → NaN | n > -1 | No `log1p` declaration cited. `Real.log (1 + x)` diverges at x = -1 (`Real.log_zero`: 0, JavaScript -∞) and for x < -1 (`Real.log_neg_eq_log`: finite, JavaScript NaN) | absent (no `Float.log1p`) | rejected |
| `Math.log2` | 21.3.2.24 `sec-math.log2` | Approximated: "Return an implementation-approximated Number value representing log2(ℝ(n))." | NaN, +∞ → n; 1 → +0; ±0 → -∞; n < -0 → NaN | n > 0 | `Real.logb 2`. Diverges at 0: `Real.logb_zero` gives 0 where JavaScript gives -∞ (`example`: logb 2 0 = 0). Diverges for x < 0: `Real.logb_neg_eq_logb` gives a finite value where JavaScript gives NaN | `Float.log2`, opaque (Float.lean:457, extern `log2`) | rejected |
| `Math.log10` | 21.3.2.23 `sec-math.log10` | Approximated: "Return an implementation-approximated Number value representing log10(ℝ(n))." | NaN, +∞ → n; 1 → +0; ±0 → -∞; n < -0 → NaN | n > 0 | `Real.logb 10`, with the same divergences as `log2` (`Real.logb_zero`, `Real.logb_neg_eq_logb`) | `Float.log10`, opaque (Float.lean:464, extern `log10`) | rejected |
| `Math.sin` | 21.3.2.31 `sec-math.sin` | Approximated: "Return an implementation-approximated Number value representing the sine of ℝ(n)." | NaN, +0, -0 → n; ±∞ → NaN | all finite n | `Real.sin`; no finite divergence | `Float.sin`, opaque (Float.lean:344, extern `sin`) | rejected |
| `Math.cos` | 21.3.2.12 `sec-math.cos` | Approximated: "Return an implementation-approximated Number value representing the cosine of ℝ(n)." | NaN, ±∞ → NaN; ±0 → 1 | all finite n | `Real.cos`; no finite divergence | `Float.cos`, opaque (Float.lean:351, extern `cos`) | rejected |
| `Math.tan` | 21.3.2.35 `sec-math.tan` | Approximated: "Return an implementation-approximated Number value representing the tangent of ℝ(n)." | NaN, +0, -0 → n; ±∞ → NaN | all finite n (every finite Number is rational and every odd multiple of π/2 is irrational, so no finite Number is a pole) | `Real.tan`. `Real.tan_pi_div_two` gives tan(π/2) = 0 where the tangent is undefined; by the argument in the previous column no finite Number input reaches that point, so this is not a divergence on Number inputs | `Float.tan`, opaque (Float.lean:358, extern `tan`) | rejected |
| `Math.atan` | 21.3.2.6 `sec-math.atan` | Approximated: "Return an implementation-approximated Number value representing the inverse tangent of ℝ(n)." | NaN, +0, -0 → n. Also approximated: +∞ → "an implementation-approximated Number value representing π / 2", -∞ → the same for -π / 2 | all finite n | `Real.arctan` (`Real.arctan_zero`); no finite divergence | `Float.atan`, opaque (Float.lean:379, extern `atan`) | rejected |
| `Math.atan2` | 21.3.2.8 `sec-math.atan2` | Approximated: "Return an implementation-approximated Number value representing r." | either argument NaN → NaN; results that are ±0 (y = ±0 with x > 0 or x = +0, and finite nonzero y with x = +∞). The ±π, ±π/2, ±π/4, ±3π/4 results for zero or infinite arguments are themselves approximated | finite (y, x) other than y = x = 0, reading y = 0 as +0 | No real `atan2` declaration cited. The analogue `Complex.arg (x + y i)` cannot see the sign of zero: `Complex.arg_zero` gives 0 for (0, 0), where JavaScript gives +0, -0, π, or -π depending on the zero signs; `Complex.arg_neg_one` gives π, matching `atan2(+0, -1)` while `atan2(-0, -1)` is -π. Unverified: that `Complex.arg` equals the specification's r on all other finite inputs; I read the definitions and did not prove it | `Float.atan2`, opaque (Float.lean:387, extern `atan2`) | rejected |
| `Math.hypot` | 21.3.2.19 `sec-math.hypot` | Approximated: "Return an implementation-approximated Number value representing the square root of the sum of squares of the mathematical values of the elements of coerced." | any ±∞ argument → +∞ (even when another argument is NaN); otherwise any NaN → NaN; all arguments ±0 → +0 | all finite arguments | No `hypot` declaration cited. `Real.sqrt (x ^ 2 + y ^ 2)` has no finite divergence on the reals; binary64 overflow in a naive evaluation is a separate issue the spec's Note warns about | absent (no `Float.hypot`) | rejected |
| `Math.imul` | 21.3.2.20 `sec-math.imul` | Exact: "Let product be (a × b) modulo 2<sup>32</sup>." then "If product ≥ 2<sup>31</sup>, return 𝔽(product - 2<sup>32</sup>)." | arguments pass through ToUint32, so NaN, ±∞, ±0 act as 0 and fractions are truncated | every input, after ToUint32 (integer arithmetic modulo 2<sup>32</sup>) | No real-number counterpart is needed. Core Lean `BitVec 32` multiplication followed by `BitVec.toInt` matches; `example`s check `imul(2 ** 31, 2) = 0` and `imul(4294967295, 5) = -5` by `decide` | absent (integer operation) | rejected |
| `Math.fround` | 21.3.2.17 `sec-math.fround` | Exact: "Let n32 be the result of converting n to IEEE 754-2019 binary32 format using roundTiesToEven mode." | NaN → NaN; +0, -0, +∞, -∞ → n | values exactly representable in binary32 (the real meaning is the identity; rounding to binary32 has no real-number counterpart) | No counterpart cited | `Float.toFloat32` (Float32.lean:555, extern `lean_float_to_float32`) then `Float32.toFloat` (Float32.lean:548), both opaque. Unverified: that the C conversion rounds ties to even in every runtime floating-point environment | rejected |
| `Math.clz32` | 21.3.2.11 `sec-math.clz32` | Exact: "Let p be the number of leading zero bits in the unsigned 32-bit binary representation of n." | argument passes through ToUint32; 0 → 32 (Note: "If n is either +0𝔽 or -0𝔽, this method returns 32𝔽.") | every input, after ToUint32 | No real-number counterpart is needed. Core Lean `BitVec.clz` on `BitVec 32` matches; `example` checks `clz32(1) = 31` and `clz32(0) = 32` by `decide` | absent (integer operation) | rejected |

Twelve members have exact finite results: `abs`, `min`, `max`, `floor`, `ceil`,
`round`, `trunc`, `sign`, `sqrt`, `imul`, `fround`, `clz32`. Fourteen rows have
approximated finite results: `cbrt`, `pow` and `**`, `exp`, `expm1`, `log`,
`log1p`, `log2`, `log10`, `sin`, `cos`, `tan`, `atan`, `atan2`, `hypot`. This
matches the list in the 21.3.2 Note for the members in scope.

## Lean `Float` inventory

Read from `~/.elan/toolchains/leanprover--lean4---v4.34.0/src/lean/Init/Data/Float/Float.lean`
and `Float32.lean`. The file's own documentation says: "From the point of view
of Lean's logic, `Float` is equivalent to `Float.Model` ... Some of the
operations on `Float` are defined in terms of their `Float.Model` counterparts,
while others are opaque to Lean's kernel."

Model-backed (`def` with a `Float.Model` body, plus `@[extern]` for compiled
code):

- arithmetic: `Float.add` (76), `Float.sub` (84), `Float.mul` (91),
  `Float.div` (101), `Float.neg` (110);
- comparison: `Float.lt` (116), `Float.le` (122), `Float.beq` (167), and the
  `Decidable` instances `Float.decLt` (177) and `Float.decLe` (185), which
  `min` and `max` use through `minOfLe` and `maxOfLe` (529, 531);
- bits and classification: `Float.ofBits` (134), `Float.toBits` (147),
  `Float.isNaN` (260), `Float.isFinite` (269), `Float.isInf` (278);
- the two `Math` counterparts with a model: `Float.sqrt` (478,
  `fun a => .ofModel a.toModel.sqrt`) and `Float.abs` (524).

Opaque (`opaque` with `@[extern]` only): `Float.sin` (344), `Float.cos` (351),
`Float.tan` (358), `Float.asin` (365), `Float.acos` (372), `Float.atan` (379),
`Float.atan2` (387), the hyperbolic functions (394 to 429), `Float.exp` (436),
`Float.exp2` (443), `Float.log` (450), `Float.log2` (457), `Float.log10` (464),
`Float.pow` (471), `Float.cbrt` (486), `Float.ceil` (498), `Float.floor` (510),
`Float.round` (517), `Float.frExp` (288), `Float.scaleB` (539),
`Float.toString` (193), and in `Float32.lean` `Float32.toFloat` (548) and
`Float.toFloat32` (555).

Absent: no declaration named `Float.trunc`, `Float.sign`, `Float.expm1`,
`Float.log1p`, or `Float.hypot` appears anywhere under the toolchain's
`src/lean` (checked with `grep -rn`). `imul` and `clz32` are integer operations;
core Lean has `BitVec.clz`.

## Lean `Float` against Node

`lean/Divergences.lean` prints each value with its binary64 bit pattern. The
Lean column is the `#eval` output from compiling that file on this machine
(arm64 macOS); the opaque rows show what the platform C library returned, which
other platforms might not reproduce exactly (unverified). The JavaScript column
is Node v24.17.0.

The first five rows are the C-versus-ECMAScript `pow` differences. The
specification's Note under 6.1.6.1.3 says: "The result of base \*\* exponent
when base is 1𝔽 or -1𝔽 and exponent is +∞𝔽 or -∞𝔽, or when base is 1𝔽 and
exponent is NaN, differs from IEEE 754-2019. The first edition of ECMAScript
specified a result of NaN for this operation, whereas later revisions of IEEE
754 specified 1𝔽. The historical ECMAScript behaviour is preserved for
compatibility reasons."

| Lean expression                   | Lean result                    | JavaScript expression | JavaScript result | Same? |
| --------------------------------- | ------------------------------ | --------------------- | ----------------- | ----- |
| `(1.0 : Float) ^ nan`             | 1 (`0x3ff0000000000000`)       | `1 ** NaN`            | NaN               | no    |
| `(1.0 : Float) ^ inf`             | 1 (`0x3ff0000000000000`)       | `1 ** Infinity`       | NaN               | no    |
| `(1.0 : Float) ^ (-inf)`          | 1 (`0x3ff0000000000000`)       | `1 ** -Infinity`      | NaN               | no    |
| `(-1.0 : Float) ^ inf`            | 1 (`0x3ff0000000000000`)       | `(-1) ** Infinity`    | NaN               | no    |
| `(-1.0 : Float) ^ (-inf)`         | 1 (`0x3ff0000000000000`)       | `(-1) ** -Infinity`   | NaN               | no    |
| `min nan 1.0`                     | 1 (`0x3ff0000000000000`)       | `Math.min(NaN, 1)`    | NaN               | no    |
| `min 1.0 nan`                     | NaN (`0x7ff8000000000000`)     | `Math.min(1, NaN)`    | NaN               | yes   |
| `max nan 1.0`                     | NaN (`0x7ff8000000000000`)     | `Math.max(NaN, 1)`    | NaN               | yes   |
| `max 1.0 nan`                     | 1 (`0x3ff0000000000000`)       | `Math.max(1, NaN)`    | NaN               | no    |
| `min (0.0 : Float) (-0.0)`        | +0 (`0x0`)                     | `Math.min(0, -0)`     | -0                | no    |
| `max (-0.0 : Float) 0.0`          | +0 (`0x0`)                     | `Math.max(-0, 0)`     | 0                 | yes   |
| `max (0.0 : Float) (-0.0)`        | -0 (`0x8000000000000000`)      | `Math.max(0, -0)`     | 0                 | no    |
| `Float.round (-2.5)`              | -3 (`0xc008000000000000`)      | `Math.round(-2.5)`    | -2                | no    |
| `Float.round 2.5`                 | 3 (`0x4008000000000000`)       | `Math.round(2.5)`     | 3                 | yes   |
| `Float.round (-0.5)`              | -1 (`0xbff0000000000000`)      | `Math.round(-0.5)`    | -0                | no    |
| `Float.sqrt (-1.0)`               | NaN (`0x7ff8000000000000`)     | `Math.sqrt(-1)`       | NaN               | yes   |
| `Float.log 0.0`                   | -inf (`0xfff0000000000000`)    | `Math.log(0)`         | -Infinity         | yes   |
| `Float.log (-1.0)`                | NaN (`0x7ff8000000000000`)     | `Math.log(-1)`        | NaN               | yes   |
| `(0.0 : Float) ^ (-1.0)`          | inf (`0x7ff0000000000000`)     | `0 ** -1`             | Infinity          | yes   |
| `nan ^ 0.0`                       | 1 (`0x3ff0000000000000`)       | `NaN ** 0`            | 1                 | yes   |

`min` and `max` on `Float` are `minOfLe` and `maxOfLe`, which return one
argument based on a single `≤` test, so the result for NaN or for a pair of
signed zeros depends on which argument comes first. ECMAScript returns NaN if
any argument is NaN and orders -0 below +0.

## Mathlib divergences

`lean/Divergences.lean` contains one compiling `example` or `#check` for every
Mathlib divergence in the table:

| Mathlib statement                                    | Evidence in `Divergences.lean`                       | JavaScript                                 |
| ---------------------------------------------------- | ---------------------------------------------------- | ------------------------------------------ |
| `0 ^ y = 0` for `y ≠ 0`                              | `Real.zero_rpow`; `example : (0 : ℝ) ^ (-1 : ℝ) = 0` | `0 ** -1` is `Infinity`                    |
| negative base, non-integral exponent is finite      | `Real.rpow_def_of_neg`; `example`s `(-1) ^ (1/2) = 0`, `(-8) ^ (1/3) = 1` | `(-1) ** 0.5` and `(-8) ** (1/3)` are NaN; `Math.cbrt(-8)` is -2 |
| `√x = 0` for `x ≤ 0`                                 | `Real.sqrt_eq_zero_of_nonpos`; `example : √(-1) = 0` | `Math.sqrt(-1)` is NaN                     |
| `log 0 = 0`                                          | `Real.log_zero`; `example`                           | `Math.log(0)` is -Infinity                 |
| `log (-x) = log x`                                   | `Real.log_neg_eq_log`; `example : log (-1) = 0`      | `Math.log(-1)` is NaN                      |
| `logb b 0 = 0`                                       | `Real.logb_zero`; `example : logb 2 0 = 0`           | `Math.log2(0)` is -Infinity                |
| `logb b (-x) = logb b x`                             | `Real.logb_neg_eq_logb` (`#check` only)              | `Math.log2(-1)` is NaN                     |
| `tan (π / 2) = 0`                                    | `Real.tan_pi_div_two` (`#check` only)                | no finite Number equals π / 2              |
| `arg 0 = 0`, `arg (-1) = π`                          | `Complex.arg_zero`, `Complex.arg_neg_one` (`#check` only) | `Math.atan2(-0, -1)` is -π; `Math.atan2(±0, ±0)` depends on the signs |

The file also records agreements used in the table: `Real.rpow_zero`,
`Real.one_rpow`, `Real.rpow_natCast` with `(-2) ^ 3 = -8`, `round_eq` with the
three rounding `example`s, and the `BitVec` `example`s for `imul` and `clz32`.

## Special-value vectors

`vectors/gen.mjs` evaluates each member on a fixed list of inputs and writes
`vectors/math-special-values.json`. It uses no randomness and no network, and
`Math.random` is excluded. The current file holds 1487 records, 1014 exact
and 473 approximated.

Inputs:

- Unary members use 32 inputs: ±0, NaN, ±∞, 1, -1, 2, -8, ±0.5, ±1.5, ±2.5,
  ±0.49999999999999994, ±`Number.MIN_VALUE`, ±`Number.MAX_VALUE`,
  2<sup>53</sup> - 1, 2<sup>53</sup>, 2<sup>53</sup> + 2, 2<sup>31</sup>,
  -2<sup>31</sup>, 2<sup>32</sup>, 4294967295, `Math.PI`, `Math.PI / 2`,
  1e-300, and 3.4028235677973366e38.
- Binary members (`pow`, `atan2`, `imul`) and the two-argument cases of the
  variadic members (`min`, `max`, `hypot`) use the 121-pair cross product of
  ±0, NaN, ±∞, ±1, ±0.5, ±2; ten subnormal and extreme pairs shared by all of
  them (`[MIN_VALUE, 2]`, `[-MIN_VALUE, 2]`, `[2, MIN_VALUE]`,
  `[2, -MIN_VALUE]`, `[MIN_VALUE, MIN_VALUE]`, `[-MIN_VALUE, -MIN_VALUE]`,
  `[MAX_VALUE, MAX_VALUE]`, `[-MAX_VALUE, MAX_VALUE]`, `[MAX_VALUE, 2]`,
  `[2, MAX_VALUE]`); and targeted pairs per member (for example
  `pow(-8, 1/3)`, `pow(2, -1075)`, `hypot(Infinity, NaN)`,
  `imul(4294967295, 5)`, `min(-0, 0)`).
- `min`, `max`, and `hypot` also get thirteen argument lists of other lengths:
  no arguments (`min` gives +∞, `max` gives -∞, `hypot` gives +0); one
  argument (NaN, -0, +0, +∞, -∞, -5); and three arguments (`[1, -0, 0]`,
  `[-0, 0, -0]`, `[1, NaN, Infinity]`, `[Infinity, NaN, 1]`,
  `[-Infinity, 1, 2]`, `[3, 4, 12]`). `inputs` in these records has 0, 1, or
  3 entries.
- Within each member, an input list that repeats an earlier one bit for bit
  (compared by `hex`, so 0 and -0 differ) is dropped, keeping the first.
- `**` has eight records for the operator form: 1 to NaN, ±1 to ±∞, NaN to 0,
  and ±0 to -1.

### Schema `lemmascript-math-vectors/1` (for #19)

The file is one JSON object:

| Field         | Meaning                                                                                         |
| ------------- | ----------------------------------------------------------------------------------------------- |
| `schema`      | the string `"lemmascript-math-vectors/1"`                                                       |
| `generator`   | the command that produced the file, `node spikes/math-semantics/vectors/gen.mjs`                |
| `engine`      | `{ "node": process.version, "v8": process.versions.v8 }`                                        |
| `specEdition` | the ECMAScript edition and fetch date the classification follows                                |
| `note`        | a reminder that approximated results are what this engine returned                              |
| `records`     | array of records, one per line in the file                                                      |

Each record:

| Field    | Meaning                                                                                                                                                                                        |
| -------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `member` | `"Math.<name>"`, or `"**"` for the exponentiation operator                                                                                                                                     |
| `inputs` | array of `{ "js", "hex" }`, in argument order                                                                                                                                                  |
| `result` | `{ "js", "hex" }`                                                                                                                                                                              |
| `class`  | `"exact"` when the specification step that produced the result fixes one Number value; `"approximated"` when that step returns an implementation-approximated Number value                     |

`js` is a JavaScript literal: `NaN`, `Infinity`, `-Infinity`, `-0`, or
`String(x)`. `hex` is the big-endian binary64 bit pattern written by
`DataView.prototype.setFloat64(0, x, false)`, as `0x` followed by 16 lowercase
hex digits.

Consumers should note two things. First, the NaN bit pattern
(`0x7ff8000000000000`) is the one V8 produced, and the specification does not
distinguish NaN payloads, so NaN results should be compared as a class.
Second, for `approximated` records the `result` is only what Node v24.17.0
returned; another engine or version may return a different Number value and
still conform. `exact` records are the ones a backend must reproduce bit for
bit. The `class` follows the spec step, so `Math.atan(Infinity)` is
`approximated` even though it is a special case. The classifier decides from
the inputs alone. For `atan2(y, x)` it marks a record exact when either
argument is NaN, when y is ±0 and x > 0 or x is +0, or when y is finite and
nonzero and x is +∞; those are the steps of 21.3.2.8 that return NaN, +0, or
-0. All other `atan2` steps, including every case with y = ±∞, are
approximated. So `atan2(MIN_VALUE, 2)` is approximated even though V8 returns
+0 for it.

Record counts by member (exact / approximated): `abs`, `floor`, `ceil`,
`round`, `trunc`, `sign`, `sqrt`, `fround`, `clz32` 32 / 0 each; `imul`
136 / 0; `min`, `max` 144 / 0 each; `**` 8 / 0; `atan` 3 / 29; `atan2`
37 / 94; `cbrt`, `cos`, `exp`, `expm1`, `sin`, `tan` 5 / 27 each; `hypot`
71 / 74; `log`, `log2`, `log10` 15 / 17 each; `log1p` 11 / 21; `pow` 97 / 42.

## Dafny status

`fixtures/run-dafny-gen.mjs <out-dir>` copies each fixture to a directory
outside the repository and runs `npx tsx tools/src/lsc.ts gen --backend=dafny`
on the copy, so no generated `.dfy` file enters the tracked tree. Each fixture
is one exported function `f`. The `int` fixtures use plain `number`, which
LemmaScript reads as `int`; the `real` fixtures add `//@ type x real` (and the
same for `y`) and `//@ type \result real`.

Emitted and checked with `dafny verify` (Dafny 4.11.0). The last column
quotes Dafny's summary line. "0 verified, 0 errors" with exit 0 means Dafny
parsed and typechecked the file and found no proof obligation, because the
fixture has no contract and returns a plain `int` or `real`.

| Fixture                    | Emitted body                                                                       | `dafny verify`                                                                              |
| -------------------------- | ---------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| `absInt.ts`                | `MathAbs(x)` with preamble `function MathAbs(x: int): nat { if x >= 0 then x else -x }` | exit 0, "1 verified, 0 errors" (the obligation is the `nat` result)                         |
| `absReal.ts`               | `MathAbsReal(x)`                                                                   | exit 0, "0 verified, 0 errors"                                                              |
| `minInt.ts`                | `MathMin(x, y)`                                                                    | exit 0, "0 verified, 0 errors"                                                              |
| `minReal.ts`               | `MathMinReal(x, y)`                                                                | exit 0, "0 verified, 0 errors"                                                              |
| `maxInt.ts`                | `MathMax(x, y)`                                                                    | exit 0, "0 verified, 0 errors"                                                              |
| `maxReal.ts`               | `MathMaxReal(x, y)`                                                                | exit 0, "0 verified, 0 errors"                                                              |
| `floorInt.ts`              | `x`                                                                                | exit 0, "0 verified, 0 errors"                                                              |
| `ceilInt.ts`               | `x`                                                                                | exit 0, "0 verified, 0 errors"                                                              |
| `floorReal.ts`             | `FloorReal(x)`, preamble `x.Floor`                                                 | exit 0, "0 verified, 0 errors"                                                              |
| `ceilReal.ts`              | `CeilReal(x)`, preamble `if x == (x.Floor as real) then x.Floor else x.Floor + 1`  | exit 0, "0 verified, 0 errors"                                                              |
| `expOpInt.ts`              | `(x ** y)`                                                                         | exit 2, `Error: invalid UnaryExpression`, "1 parse errors detected in expOpInt.dfy"         |
| `expOpReal.ts`             | `(x ** y)`                                                                         | exit 2, `Error: invalid UnaryExpression`, "1 parse errors detected in expOpReal.dfy"        |
| `floorDivInt.ts`           | `JSFloorDiv(x, y)` with `requires (y != 0)` from `//@ requires y !== 0`            | exit 0, "2 verified, 0 errors"                                                              |
| `floorDivIntUnguarded.ts`  | `JSFloorDiv(x, y)`, no `requires`                                                  | exit 4, `Error: function precondition could not be proved`, "1 verified, 1 error"           |
| `minSpreadInt.ts`          | `MinOfSeq(xs)` for `Math.min(...xs)`, `xs: seq<int>`, no `requires`                | exit 4, `Error: function precondition could not be proved`, "3 verified, 1 error"           |
| `maxSpreadIntGuarded.ts`   | `MaxOfSeq(xs)` with `requires (\|xs\| > 0)` from `//@ requires xs.length > 0`    | exit 0, "4 verified, 0 errors"                                                              |

The four fixtures in the last rows check lowerings that `transform.ts`,
`extract.ts`, and `dafny-emit.ts` perform at `60cab87`:

- `Math.floor(a / b)` with integral operands. `transform.ts` lines 893 to 908
  rewrite it to `JSFloorDiv(a, b)` for Dafny before the `real` branch is
  tried, matching the `SPEC.md` line 473 row. The preamble at `dafny-emit.ts`
  lines 1123 to 1132 has `requires b != 0`. JavaScript evaluates
  `Math.floor(1 / 0)` to +∞, `Math.floor(-1 / 0)` to -∞, `Math.floor(0 / 0)`
  to NaN, and `Math.floor(-0 / 5)` to -0. It also rounds the quotient to
  binary64 before flooring, so above 2^53 the results differ:
  `Math.floor(2 ** 60 / 3)` is 384307168202282304 (it prints as
  384307168202282300), while the integer floor of 2^60 / 3 is
  384307168202282325. The 2^53 observation comes from my Node probe; I did not
  find it documented in LemmaScript.
- Positional `Math.min` and `Math.max`. `transform.ts` lines 872 to 883 lower
  them only when the call has exactly two arguments (and `Math.abs` only with
  one). Any other arity falls through to the generic method-call path, which
  `lsc gen` rejects: `min3Int.ts` (`Math.min(x, y, z)`) exits 1 with
  `ERROR: Dafny emission failed for 'f' in min3Int.ts: Unsupported Dafny method call: .min() on unknown`.
- Spread `Math.min(...xs)` and `Math.max(...xs)`. `extract.ts` lines 479 to
  490 rewrite them to `MinOfSeq` and `MaxOfSeq` (via `buildSpreadConcat`).
  The preambles at `dafny-emit.ts` lines 1528 to 1575 take `seq<int>` and
  have `requires |s| > 0`, with lemmas `MinOfSeqConcat` and `MaxOfSeqConcat`.
  JavaScript returns +∞ for `Math.min()` and -∞ for `Math.max()` on an empty
  array, so the Dafny lowering is defined only where JavaScript returns a
  finite element, and an unguarded call leaves a precondition Dafny cannot
  prove.

Rejected by `lsc gen` (exit 1, error raised at `tools/src/dafny-emit.ts:588`):
`round`, `trunc`, and `sign` (both int and real fixtures), `sqrt`, `cbrt`, `pow`,
`exp`, `expm1`, `log`, `log1p`, `log2`, `log10`, `sin`, `cos`, `tan`, `atan`,
`atan2`, `hypot`, `imul`, `fround`, `clz32`, plus `min3Int.ts` above. The message has the form
`ERROR: Dafny emission failed for 'f' in sqrtReal.ts: Unsupported Dafny method call: .sqrt() on unknown`.

This matches `SPEC.md` at `60cab87`: its lowering table (lines 473 to 482)
lists only `floor`, `ceil`, `abs`, `min`, and `max`, and line 1522 says
"`**`, `>>>`, and `Math.round`/`trunc`/`sqrt`/`pow` have no lowering at all".
The `**` case is a mismatch with that sentence: `lsc gen` emits the operator
unchanged instead of rejecting it, and Dafny then fails to parse the output.
The preambles `MathMinReal` and `MathMaxReal` compare with `<=` and `>=` on
`real`, which has no NaN or -0, so they agree with JavaScript only on finite
arguments and never return -0.

## Evidence for `DESIGN_NUMBERS.md` §9 Question 7

Question 7 asks: "Should implementation-approximated operations stay
unsupported, use a weak engine-neutral relation, or require a separately
versioned runtime profile?" This spike records the following facts and makes
no recommendation.

- Fourteen of the 26 rows return implementation-approximated finite results.
  For those rows the specification fixes only the special cases listed in the
  table. Some special cases are themselves approximated (`atan(±∞)`, the ±π
  and ±π/2 results of `atan2`).
- For the twelve exact rows, the deciding step names a single value. For
  `sqrt` the value is 𝔽 of the real square root, and for `fround` it is
  binary32 rounding with ties to even, both of which a backend can state
  without reference to an engine.
- No backend counterpart reproduces ECMAScript on the approximated rows:
  Lean's `Float` versions are opaque calls into the C library, which follows
  IEEE 754 where ECMAScript deliberately does not (`pow`), and Mathlib's real
  functions assign finite values where ECMAScript returns NaN or -∞ (`pow`,
  `log`, `log2`, `log10`, `log1p`, and `cbrt` written with `rpow`).
- On the inputs where the real meaning applies, every approximated row has a
  Mathlib counterpart (or a composition such as `Real.exp x - 1`) whose value
  is the mathematical value the specification asks an engine to approximate.
  The specification gives no error bound for that approximation; it only
  recommends fdlibm.
- The vectors record one engine. Whether V8 and JavaScriptCore or other
  engines return different last bits on any of these inputs is unverified
  here; no second engine was run.
- Dafny at `60cab87` rejects every approximated member, and Lean
  `Float.pow`, `exp`, `log`, and the trigonometric functions cannot be unfolded
  in proofs because they are opaque.

## Reproduction

From the repository root:

```sh
# Regenerate the vectors and compare with the committed JSON (exit 1 on mismatch).
node spikes/math-semantics/vectors/gen.mjs --check

# Compile the Lean examples, checks, and #evals (exit 0, no sorry, no warnings).
lake env lean spikes/math-semantics/lean/Divergences.lean

# Run lsc gen --backend=dafny on copies of the fixtures outside the repository.
node spikes/math-semantics/fixtures/run-dafny-gen.mjs ../math-semantics-dafny-out
```

To check one emitted file with Dafny, run `dafny verify <out-dir>/<name>.dfy`.
`Divergences.lean` is not part of `lakefile.lean`; it is compiled on its own
with `lake env lean`.
