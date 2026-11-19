// Workload W1 (safe-integer loops) in Encoding C.
// Library: C_lib.dfy.
//
// The JavaScript source is the same as A_safeint.dfy. Indices are fp64
// values, so every array access needs an fp64 -> int conversion.

predicate IsSafeIntF(x: fp64) { x.IsFinite && fp64.Equal(MathTrunc(x), x) && fp64.LessOrEqual(fp64.Abs(x), 9007199254740991.0) }

function Midpoint(lo: fp64, hi: fp64): (m: fp64)
  requires IsSafeIntF(lo) && IsSafeIntF(hi)
  requires fp64.LessOrEqual(0.0, lo) && fp64.LessOrEqual(lo, hi)
  ensures IsSafeIntF(m)
  ensures fp64.LessOrEqual(lo, m) && fp64.LessOrEqual(m, hi)
  ensures fp64.Less(lo, hi) ==> fp64.Less(m, hi)
{
  Add(lo, MathTrunc(Div(Sub(hi, lo), 2.0)))
}

method BinarySearch(a: seq<fp64>, key: fp64) returns (idx: int)
  requires |a| < 4294967296
  requires forall i :: 0 <= i < |a| ==> a[i].IsFinite
  requires key.IsFinite
  requires forall i, j :: 0 <= i < j < |a| ==> fp64.LessOrEqual(a[i], a[j])
  ensures -1 <= idx < |a|
  ensures 0 <= idx ==> StrictEq(a[idx], key)
{
  var lo: fp64 := 0.0;
  var hi: fp64 := fp64.FromReal(|a| as real);
  assert hi as int == |a|; // @manual
  while Lt(lo, hi)
    invariant IsSafeIntF(lo) && IsSafeIntF(hi)
    invariant fp64.LessOrEqual(0.0, lo) && fp64.LessOrEqual(lo, hi)
    invariant hi as int <= |a|
    decreases hi as int - lo as int
  {
    var mid := Midpoint(lo, hi);
    var k := mid as int;
    if Lt(a[k], key) {
      lo := Add(mid, 1.0);
    } else if Lt(key, a[k]) {
      hi := mid;
    } else {
      return k;
    }
  }
  return -1;
}

// Accumulating fp64 values is not exact. With every element an integer in
// [0, bound] and |a| * bound <= 2^53, every partial sum is exact.
method SumBounded(a: seq<fp64>, bound: fp64) returns (s: fp64)
  requires IsSafeIntF(bound) && fp64.LessOrEqual(0.0, bound)
  requires forall i :: 0 <= i < |a| ==> IsSafeIntF(a[i]) && fp64.LessOrEqual(0.0, a[i]) && fp64.LessOrEqual(a[i], bound)
  requires (|a| as real) * (bound as real) <= 9007199254740991.0
  ensures IsSafeIntF(s)
  ensures (s as real) <= (|a| as real) * (bound as real)
{
  s := 0.0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant IsSafeIntF(s) && fp64.LessOrEqual(0.0, s)
    invariant (s as real) <= (i as real) * (bound as real)
  {
    s := Add(s, a[i]);
    i := i + 1;
  }
}
