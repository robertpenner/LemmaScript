// Workload W1 (safe-integer loops) in Encoding B.
// Library: B_lib.dfy.
//
// The JavaScript source is the same as A_safeint.dfy. Index arithmetic is
// written over Num and the integer facts are carried as predicates on the
// real payload.

predicate IsIntNum(x: Num) { x.Finite? && x.r == x.r.Floor as real }

function OfInt(i: int): Num { Lit(i as real) }

function Midpoint(lo: Num, hi: Num): (m: Num)
  requires IsIntNum(lo) && IsIntNum(hi) && 0.0 <= lo.r <= hi.r
  ensures IsIntNum(m)
  ensures lo.r <= m.r <= hi.r
  ensures lo.r < hi.r ==> m.r < hi.r
{
  SubFinite(hi, lo); // @manual
  var d := Sub(hi, lo);
  DivFinite(d, Lit(2.0)); // @manual
  var h := Div(d, Lit(2.0));
  var t := MathTrunc(h);
  HalfFloorBounds(hi.r.Floor - lo.r.Floor); // @manual
  assert (hi.r.Floor - lo.r.Floor) as real == hi.r - lo.r; // @manual
  assert t.Finite? && t.r == ((hi.r - lo.r) / 2.0).Floor as real; // @manual
  AddFinite(lo, t); // @manual
  IntSum(lo.r.Floor, ((hi.r - lo.r) / 2.0).Floor); // @manual
  Add(lo, t)
}

lemma SubFinite(x: Num, y: Num) // @lemma
  requires x.Finite? && y.Finite?
  ensures Sub(x, y).Finite? && Sub(x, y).r == x.r - y.r
{
}

lemma AddFinite(x: Num, y: Num) // @lemma
  requires x.Finite? && y.Finite?
  ensures Add(x, y).Finite? && Add(x, y).r == x.r + y.r
{
}

lemma DivFinite(x: Num, y: Num) // @lemma
  requires x.Finite? && y.Finite? && y.r != 0.0
  ensures Div(x, y).Finite? && Div(x, y).r == x.r / y.r
{
}

lemma IntSum(a: int, b: int) // @lemma
  ensures (a as real + b as real).Floor == a + b
{
  assert a as real + b as real == (a + b) as real; // @manual
}

lemma HalfFloorBounds(n: int) // @lemma
  requires n >= 0
  ensures 0 <= ((n as real) / 2.0).Floor <= n
  ensures n > 0 ==> ((n as real) / 2.0).Floor < n
{
}

lemma IntNumSucc(x: Num) // @lemma
  requires IsIntNum(x)
  ensures IsIntNum(Lit(x.r + 1.0))
{
  assert x.r + 1.0 == (x.r.Floor + 1) as real; // @manual
}

method BinarySearch(a: seq<Num>, key: Num) returns (idx: int)
  requires forall i :: 0 <= i < |a| ==> a[i].Finite?
  requires key.Finite?
  requires forall i, j :: 0 <= i < j < |a| ==> a[i].r <= a[j].r
  ensures -1 <= idx < |a|
  ensures 0 <= idx ==> StrictEq(a[idx], key)
  ensures idx < 0 ==> forall i :: 0 <= i < |a| ==> !StrictEq(a[i], key)
{
  var lo := OfInt(0);
  var hi := OfInt(|a|);
  while Lt(lo, hi)
    invariant IsIntNum(lo) && IsIntNum(hi)
    invariant 0.0 <= lo.r <= hi.r <= |a| as real
    invariant forall i :: 0 <= i < |a| && (i as real) < lo.r ==> a[i].r < key.r
    invariant forall i :: 0 <= i < |a| && hi.r <= (i as real) ==> a[i].r > key.r
    decreases hi.r.Floor - lo.r.Floor
  {
    var mid := Midpoint(lo, hi);
    var k := mid.r.Floor;
    assert k as real == mid.r; // @manual
    if Lt(a[k], key) {
      IntNumSucc(mid); // @manual
      AddFinite(mid, Lit(1.0)); // @manual
      lo := Add(mid, Lit(1.0));
    } else if Lt(key, a[k]) {
      hi := mid;
    } else {
      return k;
    }
  }
  return -1;
}

function SumR(a: seq<Num>): real
  requires forall i :: 0 <= i < |a| ==> a[i].Finite?
{
  if |a| == 0 then 0.0 else SumR(a[..|a| - 1]) + a[|a| - 1].r
}

// No range precondition is needed: Encoding B has no overflow and no
// rounding, so the accumulator is always exact.
method SumBounded(a: seq<Num>) returns (s: Num)
  requires forall i :: 0 <= i < |a| ==> a[i].Finite? && !a[i].negZero
  ensures s.Finite? && s.r == SumR(a)
{
  s := PosZero;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant s.Finite? && s.r == SumR(a[..i])
  {
    assert a[..i + 1][..i] == a[..i]; // @manual
    s := Add(s, a[i]);
    i := i + 1;
  }
  assert a[..|a|] == a; // @manual
}
