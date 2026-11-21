// Workload W5 (lerp and representation bridges) in Encoding B.
// Library: B_lib.dfy.
//
//   function lerp(a, b, t) { return a + t * (b - a); }
//
// Encoding B has exact real arithmetic, so it proves properties that
// JavaScript doubles violate. Each lemma below that states such a property
// names the JavaScript counterexample next to it.

function Lerp(a: Num, b: Num, t: Num): Num { Add(a, Mul(t, Sub(b, a))) }

lemma FiniteOps(x: Num, y: Num) // @helper
  requires x.Finite? && y.Finite?
  ensures Add(x, y).Finite? && Add(x, y).r == x.r + y.r
  ensures Sub(x, y).Finite? && Sub(x, y).r == x.r - y.r
  ensures Mul(x, y).Finite? && Mul(x, y).r == x.r * y.r
{
}

lemma MulBetween(t: real, d: real) // @helper
  requires 0.0 <= t <= 1.0 && 0.0 <= d
  ensures 0.0 <= t * d <= d
{
  MulNonneg(t, d); // @manual
  MulNonneg(1.0 - t, d); // @manual
  assert d - t * d == (1.0 - t) * d; // @manual
}

lemma MulNonneg(x: real, y: real) // @helper
  requires 0.0 <= x && 0.0 <= y
  ensures 0.0 <= x * y
{
}

// Holds in B. In JavaScript, lerp(-Number.MAX_VALUE, Number.MAX_VALUE, 0) is
// NaN because b - a overflows to Infinity and 0 * Infinity is NaN.
lemma LerpInRange(a: Num, b: Num, t: Num) // @target
  requires a.Finite? && b.Finite? && t.Finite?
  requires a.r <= b.r && 0.0 <= t.r <= 1.0
  ensures Lerp(a, b, t).Finite?
  ensures a.r <= Lerp(a, b, t).r <= b.r
{
  var d := Sub(b, a);
  FiniteOps(b, a); // @manual
  var m := Mul(t, d);
  FiniteOps(t, d); // @manual
  FiniteOps(a, m); // @manual
  MulBetween(t.r, d.r); // @manual
  assert 0.0 <= m.r <= d.r; // @manual
}

// Holds in B. In JavaScript, lerp(-3.5046841142397023, 4.999795502080206, 1)
// is 4.9997955020802065, one ulp above b.
lemma LerpAtOne(a: Num, b: Num) // @target
  requires a.Finite? && b.Finite? && !b.negZero
  ensures Lerp(a, b, Lit(1.0)) == b
{
  FiniteOps(b, a); // @manual
  FiniteOps(Lit(1.0), Sub(b, a)); // @manual
  FiniteOps(a, Mul(Lit(1.0), Sub(b, a))); // @manual
}

const MAX_VALUE: real := 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0

lemma LerpExtremesInB() // @target
  ensures Lerp(Lit(-MAX_VALUE), Lit(MAX_VALUE), PosZero) == Lit(-MAX_VALUE)
{
  FiniteOps(Lit(MAX_VALUE), Lit(-MAX_VALUE)); // @manual
}

// Bridges between Num and the int and real views that other proofs use.
predicate IsIntNum(x: Num) { x.Finite? && x.r == x.r.Floor as real }

function ToIntBridge(x: Num): int
  requires IsIntNum(x)
{
  x.r.Floor
}

function FromIntBridge(i: int): (x: Num)
  ensures IsIntNum(x)
{
  Lit(i as real)
}

lemma BridgeRoundTrip(i: int) // @target
  ensures ToIntBridge(FromIntBridge(i)) == i
{
}

lemma BridgeAdd(i: int, j: int) // @target
  requires i + j != 0
  ensures Add(FromIntBridge(i), FromIntBridge(j)) == FromIntBridge(i + j)
{
}

lemma BridgeMul(i: int, j: int) // @target
  requires i != 0 && j != 0
  ensures Mul(FromIntBridge(i), FromIntBridge(j)) == FromIntBridge(i * j)
{
}
