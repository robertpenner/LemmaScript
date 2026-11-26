// Workload W2 (NaN-sensitive clamp and guards) in Encoding C.
// Library: C_lib.dfy.
//
//   function clamp(x, lo, hi) { return x < lo ? lo : x > hi ? hi : x; }
//   function clampNeg(x, lo, hi) { return !(x >= lo) ? lo : !(x <= hi) ? hi : x; }
//   function clampMM(x, lo, hi) { return Math.min(Math.max(x, lo), hi); }
//
// Ghost `==` on fp64 is representation identity (NaN == NaN, +0 != -0), so
// the lemmas below state exact JS results with `==`.

function Clamp(x: fp64, lo: fp64, hi: fp64): fp64
{
  if Lt(x, lo) then lo else if Gt(x, hi) then hi else x
}

function ClampNeg(x: fp64, lo: fp64, hi: fp64): fp64
{
  if !Ge(x, lo) then lo else if !Le(x, hi) then hi else x
}

function ClampMM(x: fp64, lo: fp64, hi: fp64): fp64
{
  MathMin(MathMax(x, lo), hi)
}

lemma NaNSeparatesGuards() // @target
  ensures Clamp(fp64.NaN, 0.0, 1.0).IsNaN
  ensures ClampNeg(fp64.NaN, 0.0, 1.0) == 0.0
  ensures ClampMM(fp64.NaN, 0.0, 1.0).IsNaN
{
}

lemma ClampInRange(x: fp64, lo: fp64, hi: fp64) // @target
  requires lo.IsFinite && hi.IsFinite && Le(lo, hi)
  requires !x.IsNaN
  ensures var r := Clamp(x, lo, hi); r.IsFinite && Le(lo, r) && Le(r, hi)
{
}

lemma ClampNegInRange(x: fp64, lo: fp64, hi: fp64) // @target
  requires lo.IsFinite && hi.IsFinite && Le(lo, hi)
  ensures var r := ClampNeg(x, lo, hi); r.IsFinite && Le(lo, r) && Le(r, hi)
{
}

lemma GuardsAgreeOffNaN(x: fp64, lo: fp64, hi: fp64) // @target
  requires !x.IsNaN && !lo.IsNaN && !hi.IsNaN
  ensures Clamp(x, lo, hi) == ClampNeg(x, lo, hi)
{
}

lemma ClampKeepsNegZero() // @target
  ensures Clamp(fp64.Neg(0.0), 0.0, 1.0) == fp64.Neg(0.0)
  ensures ClampMM(fp64.Neg(0.0), 0.0, 1.0) == 0.0
{
}
