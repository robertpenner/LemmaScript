// Workload W3 (signed zero) in Encoding B.
// Library: B_lib.dfy.
//
//   1 / x, Math.min(+0, -0), Object.is, SameValueZero (Map keys, includes)

lemma ReciprocalOfZeros() // @lemma
  ensures Div(Lit(1.0), PosZero) == PosInf
  ensures Div(Lit(1.0), NegZero) == NegInf
  ensures Div(PosZero, PosZero) == NaN
{
}

lemma MinMaxZeros() // @lemma
  ensures MathMin(PosZero, NegZero) == NegZero
  ensures MathMin(NegZero, PosZero) == NegZero
  ensures MathMax(PosZero, NegZero) == PosZero
{
}

lemma EqualityRelations() // @lemma
  ensures StrictEq(PosZero, NegZero)
  ensures !ObjectIs(PosZero, NegZero)
  ensures SameValueZero(PosZero, NegZero)
  ensures !StrictEq(NaN, NaN)
  ensures ObjectIs(NaN, NaN)
  ensures SameValueZero(NaN, NaN)
{
}

// SameValueZero is an equivalence relation, which is what Map and Set need.
lemma SameValueZeroEquivalence(x: Num, y: Num, z: Num) // @lemma
  ensures SameValueZero(x, x)
  ensures SameValueZero(x, y) ==> SameValueZero(y, x)
  ensures SameValueZero(x, y) && SameValueZero(y, z) ==> SameValueZero(x, z)
{
}

// Normalizing a key with `k === 0 ? 0 : k` (or `k + 0`) maps SameValueZero
// classes onto ObjectIs classes.
function NormKey(k: Num): Num { if StrictEq(k, PosZero) then PosZero else k }

lemma NormKeyCollapses(x: Num, y: Num) // @lemma
  ensures SameValueZero(x, y) <==> ObjectIs(NormKey(x), NormKey(y))
{
}

lemma AddZeroNormalizes(x: Num) // @lemma
  ensures ObjectIs(Add(x, PosZero), NormKey(x))
{
}

// Products and quotients of zeros pick the XOR sign.
lemma ZeroSigns(x: Num) // @lemma
  requires x.Finite? && x.r < 0.0
  ensures Mul(x, PosZero) == NegZero
  ensures Div(PosZero, x) == NegZero
  ensures MathRound(Lit(-0.25)) == NegZero
  ensures MathTrunc(Lit(-0.5)) == NegZero
{
}

lemma RemSign() // @lemma
  ensures Rem(Lit(-4.0), Lit(2.0)) == NegZero
  ensures Rem(Lit(-5.0), Lit(2.0)) == Lit(-1.0)
  ensures Rem(Lit(5.5), Lit(-2.0)) == Lit(1.5)
{
}
