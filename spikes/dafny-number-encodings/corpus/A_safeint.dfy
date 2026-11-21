// Workload W1 (safe-integer loops) in Encoding A.
// Library: A_lib.dfy (passed with --library by run.sh).
//
//   function midpoint(lo, hi) { return lo + Math.trunc((hi - lo) / 2); }
//   function binarySearch(a, key) { let lo = 0, hi = a.length; ... }
//   function sumBounded(a, bound) { let s = 0; for (...) s += a[i]; return s; }

function Midpoint(lo: SafeInt, hi: SafeInt): (m: SafeInt)
  requires 0 <= lo <= hi
  ensures lo <= m <= hi
  ensures lo < hi ==> m < hi
{
  lo + JSTruncDiv((hi - lo) as int, 2) as SafeInt
}

// The naive form `(lo + hi) / 2` carries an overflow obligation on `lo + hi`.
function MidpointNaive(lo: SafeInt, hi: SafeInt): (m: SafeInt)
  requires 0 <= lo <= hi
  requires lo as int + hi as int <= MAX_SAFE
  ensures lo <= m <= hi
{
  JSTruncDiv((lo + hi) as int, 2) as SafeInt
}

method BinarySearch(a: seq<SafeInt>, key: SafeInt) returns (idx: SafeInt)
  requires |a| < TWO32
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
  ensures -1 <= idx as int < |a|
  ensures 0 <= idx ==> a[idx] == key
  ensures idx < 0 ==> key !in a
{
  var lo: SafeInt := 0;
  var hi: SafeInt := |a| as SafeInt;
  while lo < hi
    invariant 0 <= lo as int <= hi as int <= |a|
    invariant forall i :: 0 <= i < lo as int ==> a[i] < key
    invariant forall i :: hi as int <= i < |a| ==> a[i] > key
    decreases hi - lo
  {
    var mid := Midpoint(lo, hi);
    if a[mid] < key {
      lo := mid + 1;
    } else if a[mid] > key {
      hi := mid;
    } else {
      return mid;
    }
  }
  return -1;
}

lemma MulMonotone(x: int, y: int, b: int) // @helper
  requires 0 <= x <= y && 0 <= b
  ensures x * b <= y * b
{
}

method SumBounded(a: seq<SafeInt>, bound: SafeInt) returns (s: SafeInt)
  requires 0 <= bound
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i] <= bound
  requires |a| * bound as int <= MAX_SAFE
  ensures s as int == Sum(seq(|a|, i requires 0 <= i < |a| => a[i] as int))
  ensures s as int <= |a| * bound as int
{
  ghost var xs := seq(|a|, i requires 0 <= i < |a| => a[i] as int);
  s := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= s as int <= i * bound as int
    invariant s as int == Sum(xs[..i])
  {
    MulMonotone(i + 1, |a|, bound as int); // @manual
    assert xs[..i + 1][..i] == xs[..i]; // @manual
    s := s + a[i];
    i := i + 1;
  }
  assert xs[..|a|] == xs; // @manual
}
