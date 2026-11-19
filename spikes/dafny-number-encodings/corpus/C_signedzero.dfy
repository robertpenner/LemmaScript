// Workload W3 (signed zero) in Encoding C.
// Library: C_lib.dfy.
//
//   1 / x, Math.min(+0, -0), Object.is, SameValueZero (Map keys, includes)
//
// JavaScript `%` has no counterpart: Dafny's fp64 has no remainder
// operation, so the RemSign lemma from B_signedzero.dfy is not ported.

lemma ReciprocalOfZeros() // @lemma
  ensures Div(1.0, 0.0) == fp64.PositiveInfinity
  ensures Div(1.0, fp64.Neg(0.0)) == fp64.NegativeInfinity
  ensures Div(0.0, 0.0).IsNaN
{
}

lemma MinMaxZeros() // @lemma
  ensures MathMin(0.0, fp64.Neg(0.0)) == fp64.Neg(0.0)
  ensures MathMin(fp64.Neg(0.0), 0.0) == fp64.Neg(0.0)
  ensures MathMax(0.0, fp64.Neg(0.0)) == 0.0
{
}

lemma EqualityRelations() // @lemma
  ensures StrictEq(0.0, fp64.Neg(0.0))
  ensures !ObjectIs(0.0, fp64.Neg(0.0))
  ensures SameValueZero(0.0, fp64.Neg(0.0))
  ensures !StrictEq(fp64.NaN, fp64.NaN)
  ensures ObjectIs(fp64.NaN, fp64.NaN)
  ensures SameValueZero(fp64.NaN, fp64.NaN)
{
}

lemma SameValueZeroEquivalence(x: fp64, y: fp64, z: fp64) // @lemma
  ensures SameValueZero(x, x)
  ensures SameValueZero(x, y) ==> SameValueZero(y, x)
  ensures SameValueZero(x, y) && SameValueZero(y, z) ==> SameValueZero(x, z)
{
}

// Dafny's own Object.is is ghost `==`; the compiled ObjectIs in C_lib.dfy
// must agree with it.
lemma ObjectIsIsIdentity(x: fp64, y: fp64) // @lemma
  ensures ObjectIs(x, y) <==> (x == y || (x.IsNaN && y.IsNaN))
{
}

function NormKey(k: fp64): fp64 { if StrictEq(k, 0.0) then 0.0 else k }

lemma NormKeyCollapses(x: fp64, y: fp64) // @lemma
  ensures SameValueZero(x, y) <==> ObjectIs(NormKey(x), NormKey(y))
{
}

lemma AddZeroNormalizes(x: fp64) // @lemma
  ensures ObjectIs(Add(x, 0.0), NormKey(x))
{
}

lemma ZeroSigns(x: fp64) // @lemma
  requires x.IsFinite && Lt(x, 0.0)
  ensures Mul(x, 0.0) == fp64.Neg(0.0)
  ensures Div(0.0, x) == fp64.Neg(0.0)
  ensures MathRound(-0.25) == fp64.Neg(0.0)
  ensures MathTrunc(-0.5) == fp64.Neg(0.0)
{
}
