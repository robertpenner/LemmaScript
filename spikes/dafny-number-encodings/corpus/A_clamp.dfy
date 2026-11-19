// Workload W2 (clamp and comparison guards) in Encoding A.
// Library: A_lib.dfy.
//
//   function clamp(x, lo, hi) { return x < lo ? lo : x > hi ? hi : x; }
//   function clampNeg(x, lo, hi) { return !(x >= lo) ? lo : !(x <= hi) ? hi : x; }
//
// SafeInt has no NaN, so the two guard forms are interchangeable here and the
// NaN case that separates them in JavaScript cannot be stated.

function Clamp(x: SafeInt, lo: SafeInt, hi: SafeInt): (r: SafeInt)
  requires lo <= hi
  ensures lo <= r <= hi
  ensures lo <= x <= hi ==> r == x
{
  if x < lo then lo else if x > hi then hi else x
}

function ClampNeg(x: SafeInt, lo: SafeInt, hi: SafeInt): SafeInt
{
  if !(x >= lo) then lo else if !(x <= hi) then hi else x
}

lemma GuardFormsAgree(x: SafeInt, lo: SafeInt, hi: SafeInt) // @target
  requires lo <= hi
  ensures Clamp(x, lo, hi) == ClampNeg(x, lo, hi)
{
}

function MathMin(a: SafeInt, b: SafeInt): SafeInt { if a <= b then a else b }
function MathMax(a: SafeInt, b: SafeInt): SafeInt { if a >= b then a else b }

lemma ClampIsMinMax(x: SafeInt, lo: SafeInt, hi: SafeInt) // @target
  requires lo <= hi
  ensures Clamp(x, lo, hi) == MathMin(MathMax(x, lo), hi)
{
}

// `a - b` can leave the safe range even when both operands are safe, so a
// comparison written as a subtraction needs an explicit range precondition.
function CompareBySub(a: SafeInt, b: SafeInt): SafeInt
  requires IsSafe(a as int - b as int)
{
  a - b
}
