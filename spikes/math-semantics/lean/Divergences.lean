/-
Divergences between Mathlib's real-number functions and JavaScript `Math.*`,
plus `#eval` demonstrations of Lean `Float` behaviour that differs from
ECMAScript.

Spike for robertpenner/LemmaScript#23. See ../README.md for the table that
cites each declaration checked below. The JavaScript results quoted in the
comments come from Node v24.17.0 (V8 13.6.233.17-node.49); the README lists
the exact commands.

Compile from the repository root:
  lake env lean spikes/math-semantics/lean/Divergences.lean
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Order.Round
import Mathlib.Basic.Real.Sign

/-! ## Declarations cited in the README -/

-- Definitions named in the table's Mathlib column.
#check @Real.rpow
#check @Real.sqrt
#check @Real.exp
#check @Real.log
#check @Real.logb
#check @Real.sin
#check @Real.cos
#check @Real.tan
#check @Real.arctan
#check @Real.sign
#check @Complex.arg
#check @round
#check @abs
#check @min
#check @max
-- Lemmas cited for agreements and divergences.
#check @Real.zero_rpow
#check @Real.rpow_zero
#check @Real.one_rpow
#check @Real.rpow_def_of_neg
#check @Real.rpow_def_of_pos
#check @Real.sqrt_eq_zero_of_nonpos
#check @Real.log_zero
#check @Real.log_neg_eq_log
#check @Real.logb_zero
#check @Real.logb_neg_eq_logb
#check @Real.rpow_natCast
#check @Real.arctan_zero
#check @Real.tan_pi_div_two
#check @Real.sign_zero
#check @Complex.arg_zero
#check @Complex.arg_neg_one
#check @round_eq
#check @Int.floor
#check @Int.ceil
#check @BitVec.clz
#check @Float.toFloat32
#check @Float32.toFloat

/-! ## Mathlib totalizations that disagree with JavaScript

Mathlib makes partial real functions total by choosing a junk value at points
outside the mathematical domain. JavaScript returns `NaN` or an infinity at
those points. Each example below is a proved fact about Mathlib's definition;
the comment gives what JavaScript returns for the corresponding Number inputs. -/

/-- JavaScript: `0 ** -1` and `Math.pow(0, -1)` are `Infinity`. -/
example : (0 : ℝ) ^ (-1 : ℝ) = 0 := Real.zero_rpow (by norm_num)

/-- JavaScript: `Math.sqrt(-1)` is `NaN`. -/
example : Real.sqrt (-1) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-- JavaScript: `Math.log(0)` is `-Infinity`. -/
example : Real.log 0 = 0 := Real.log_zero

/-- JavaScript: `Math.log(-1)` is `NaN`. Mathlib's `log` is `log |x|`. -/
example : Real.log (-1) = 0 := by
  rw [Real.log_neg_eq_log, Real.log_one]

/-- JavaScript: `Math.log2(0)` is `-Infinity`. -/
example : Real.logb 2 0 = 0 := Real.logb_zero

/-- JavaScript: `(-1) ** 0.5` is `NaN`. Mathlib defines `x ^ y` for `x < 0` as
`exp (log x * y) * cos (y * π)`. -/
example : (-1 : ℝ) ^ ((1 : ℝ) / 2) = 0 := by
  rw [Real.rpow_def_of_neg (by norm_num), Real.log_neg_eq_log, Real.log_one, zero_mul,
    Real.exp_zero, one_mul, show (1 : ℝ) / 2 * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two]

/-- JavaScript: `(-8) ** (1/3)` is `NaN`, and `Math.cbrt(-8)` is `-2`.
Mathlib's `(-8) ^ (1/3)` is `1`, so `rpow` with exponent `1/3` is not a cube
root for negative bases. -/
example : (-8 : ℝ) ^ ((1 : ℝ) / 3) = 1 := by
  have h8 : Real.exp (Real.log 8 * ((1 : ℝ) / 3)) = 2 := by
    rw [← Real.rpow_def_of_pos (by norm_num),
      show (8 : ℝ) = (2 : ℝ) ^ ((3 : ℕ) : ℝ) by rw [Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Real.rpow_def_of_neg (by norm_num), Real.log_neg_eq_log, h8,
    show (1 : ℝ) / 3 * Real.pi = Real.pi / 3 by ring, Real.cos_pi_div_three]
  norm_num

/-! ## Agreements on the real domain

On finite inputs inside the mathematical domain, these Mathlib facts agree with
the JavaScript result once signed zero is ignored. -/

/-- JavaScript: `NaN ** 0`, `Infinity ** 0` and every finite `x ** 0` are `1`.
On reals, `x ^ 0 = 1` for every `x`. -/
example (x : ℝ) : x ^ (0 : ℝ) = 1 := Real.rpow_zero x

/-- JavaScript: `1 ** y` is `1` for every finite `y`, but `NaN` for
`y = ±Infinity` or `NaN`. Reals contain neither, so `Real.one_rpow` matches only
the finite part. -/
example (y : ℝ) : (1 : ℝ) ^ y = 1 := Real.one_rpow y

/-- `round` in Mathlib is `⌊x + 1/2⌋`: ties go toward `+∞`, as in `Math.round`.
JavaScript: `Math.round(-2.5)` is `-2`, `Math.round(2.5)` is `3`,
`Math.round(-0.5)` is `-0` (Mathlib's integer result has no sign of zero). -/
example : round (-2.5 : ℝ) = -2 ∧ round (2.5 : ℝ) = 3 ∧ round (-0.5 : ℝ) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [round_eq] <;> norm_num

/-- JavaScript: `(-2) ** 3` is `-8`. For a negative base and an integral
exponent, Mathlib's `rpow` agrees with the integer power. -/
example : (-2 : ℝ) ^ ((3 : ℕ) : ℝ) = -8 := by
  rw [Real.rpow_natCast]; norm_num

/-! ## Integer and bit-level members

`Math.imul` and `Math.clz32` act on the 32-bit pattern produced by `ToUint32`.
Lean's `BitVec 32` reproduces them on integral inputs; these examples are
checked by `decide`. -/

/-- JavaScript: `Math.imul(2 ** 31, 2)` is `0`. -/
example : (BitVec.ofNat 32 (2 ^ 31) * BitVec.ofNat 32 2).toInt = 0 := by decide

/-- JavaScript: `Math.imul(4294967295, 5)` is `-5`. -/
example : (BitVec.ofNat 32 4294967295 * BitVec.ofNat 32 5).toInt = -5 := by decide

/-- JavaScript: `Math.clz32(1)` is `31` and `Math.clz32(0)` is `32`. -/
example : (BitVec.clz (BitVec.ofNat 32 1)).toNat = 31 ∧ (BitVec.clz (BitVec.ofNat 32 0)).toNat = 32 := by
  decide

/-! ## Lean `Float` against JavaScript

`#eval` runs the native implementation behind each `@[extern]` on this machine.
`Float.pow` calls C `pow`, which follows IEEE 754 / C99 Annex F: `pow(1, y)` is
`1` for any `y` and `pow(-1, ±∞)` is `1`. ECMAScript's Number::exponentiate
returns `NaN` in all five cases below (see the Note under 6.1.6.1.3). -/

def nan : Float := 0.0 / 0.0
def inf : Float := 1.0 / 0.0

/-- Prints the value and its binary64 bit pattern in hex. -/
def showBits (x : Float) : String :=
  s!"{x} (0x{String.ofList (Nat.toDigits 16 x.toBits.toNat)})"

-- Lean prints 1 (0x3ff0000000000000). JavaScript `1 ** NaN` is NaN.
#eval showBits ((1.0 : Float) ^ nan)
-- Lean prints 1. JavaScript `1 ** Infinity` is NaN.
#eval showBits ((1.0 : Float) ^ inf)
-- Lean prints 1. JavaScript `1 ** -Infinity` is NaN.
#eval showBits ((1.0 : Float) ^ (-inf))
-- Lean prints 1. JavaScript `(-1) ** Infinity` is NaN.
#eval showBits ((-1.0 : Float) ^ inf)
-- Lean prints 1. JavaScript `(-1) ** -Infinity` is NaN.
#eval showBits ((-1.0 : Float) ^ (-inf))

/-! `Min Float` and `Max Float` are `minOfLe` and `maxOfLe`, built on the
model-backed `Float.le`: `min x y = if x ≤ y then x else y` and
`max x y = if x ≤ y then y else x`. JavaScript `Math.min` and `Math.max` return
`NaN` if any argument is `NaN` and order `-0` below `+0`. The Lean result
therefore depends on argument order. -/

-- Lean prints 1. JavaScript `Math.min(NaN, 1)` is NaN.
#eval showBits (min nan 1.0)
-- Lean prints NaN. JavaScript `Math.min(1, NaN)` is NaN.
#eval showBits (min 1.0 nan)
-- Lean prints NaN. JavaScript `Math.max(NaN, 1)` is NaN.
#eval showBits (max nan 1.0)
-- Lean prints 1. JavaScript `Math.max(1, NaN)` is NaN.
#eval showBits (max 1.0 nan)
-- Lean prints +0 (0x0). JavaScript `Math.min(0, -0)` is -0.
#eval showBits (min (0.0 : Float) (-0.0))
-- Lean prints +0 (0x0). JavaScript `Math.max(-0, 0)` is 0.
#eval showBits (max (-0.0 : Float) 0.0)
-- Lean prints -0 (0x8000000000000000). JavaScript `Math.max(0, -0)` is 0.
#eval showBits (max (0.0 : Float) (-0.0))

/-! `Float.round` calls C `round`, which rounds halfway cases away from zero.
`Math.round` rounds them toward `+∞`. -/

-- Lean prints -3. JavaScript `Math.round(-2.5)` is -2.
#eval showBits (Float.round (-2.5))
-- Lean prints 3. JavaScript `Math.round(2.5)` is 3.
#eval showBits (Float.round 2.5)
-- Lean prints -1. JavaScript `Math.round(-0.5)` is -0.
#eval showBits (Float.round (-0.5))

/-! Cases where Lean `Float` agrees with JavaScript. -/

-- Lean prints NaN. JavaScript `Math.sqrt(-1)` is NaN.
#eval showBits (Float.sqrt (-1.0))
-- Lean prints -inf. JavaScript `Math.log(0)` is -Infinity.
#eval showBits (Float.log 0.0)
-- Lean prints NaN. JavaScript `Math.log(-1)` is NaN.
#eval showBits (Float.log (-1.0))
-- Lean prints inf. JavaScript `0 ** -1` is Infinity.
#eval showBits ((0.0 : Float) ^ (-1.0))
-- Lean prints 1. JavaScript `NaN ** 0` is 1.
#eval showBits (nan ^ 0.0)
