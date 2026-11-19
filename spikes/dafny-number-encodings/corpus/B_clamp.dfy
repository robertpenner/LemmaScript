// Workload W2 (NaN-sensitive clamp and guards) in Encoding B.
// Library: B_lib.dfy.
//
//   function clamp(x, lo, hi) { return x < lo ? lo : x > hi ? hi : x; }
//   function clampNeg(x, lo, hi) { return !(x >= lo) ? lo : !(x <= hi) ? hi : x; }
//   function clampMM(x, lo, hi) { return Math.min(Math.max(x, lo), hi); }

function Clamp(x: Num, lo: Num, hi: Num): Num
{
  if Lt(x, lo) then lo else if Gt(x, hi) then hi else x
}

function ClampNeg(x: Num, lo: Num, hi: Num): Num
{
  if !Ge(x, lo) then lo else if !Le(x, hi) then hi else x
}

function ClampMM(x: Num, lo: Num, hi: Num): Num
{
  MathMin(MathMax(x, lo), hi)
}

// JS: clamp(NaN, 0, 1) is NaN, clampNeg(NaN, 0, 1) is 0, clampMM is NaN.
lemma NaNSeparatesGuards() // @lemma
  ensures Clamp(NaN, PosZero, Lit(1.0)) == NaN
  ensures ClampNeg(NaN, PosZero, Lit(1.0)) == PosZero
  ensures ClampMM(NaN, PosZero, Lit(1.0)) == NaN
{
}

lemma ClampInRange(x: Num, lo: Num, hi: Num) // @lemma
  requires lo.Finite? && hi.Finite? && lo.r <= hi.r
  requires !x.NaN?
  ensures var r := Clamp(x, lo, hi); r.Finite? && lo.r <= r.r <= hi.r
{
}

lemma ClampNegInRange(x: Num, lo: Num, hi: Num) // @lemma
  requires lo.Finite? && hi.Finite? && lo.r <= hi.r
  ensures var r := ClampNeg(x, lo, hi); r.Finite? && lo.r <= r.r <= hi.r
{
}

// Off NaN the guard forms agree; at signed zeros they still may differ in
// sign: clamp(-0, +0, 1) is -0 for both because -0 < +0 is false.
lemma GuardsAgreeOffNaN(x: Num, lo: Num, hi: Num) // @lemma
  requires !x.NaN? && !lo.NaN? && !hi.NaN?
  ensures Clamp(x, lo, hi) == ClampNeg(x, lo, hi)
{
}

lemma ClampKeepsNegZero() // @lemma
  ensures Clamp(NegZero, PosZero, Lit(1.0)) == NegZero
  ensures ClampMM(NegZero, PosZero, Lit(1.0)) == PosZero
{
}
