// Workload W5 (lerp and representation bridges) in Encoding C.
// Library: C_lib.dfy.
//
//   function lerp(a, b, t) { return a + t * (b - a); }
//
// Encoding C models IEEE binary64, so the JavaScript counterexamples to the
// real-number lemmas in B_lerp.dfy should be provable here. Witness
// literals are written as exact decimal expansions of the doubles, so no
// `~` rounding is involved.

function Lerp(a: fp64, b: fp64, t: fp64): fp64 { Add(a, Mul(t, Sub(b, a))) }

// Number.MAX_VALUE, exactly.
const MAX_VALUE: fp64 := 179769313486231570814527423731704356798070567525844996598917476803157260780028538760589558632766878171540458953514382464234321326889464182768467546703537516986049910576551282076245490090389328944075868508455133942304583236903222948165808559332123348274797826204144723168738177180919299881250404026184124858368.0

// JS: lerp(-Number.MAX_VALUE, Number.MAX_VALUE, 0) is NaN.
lemma LerpExtremesIsNaN() // @lemma
  ensures Sub(MAX_VALUE, Neg(MAX_VALUE)) == fp64.PositiveInfinity
  ensures Lerp(Neg(MAX_VALUE), MAX_VALUE, 0.0).IsNaN
{
}

// JS: lerp(-3.5046841142397023, 4.999795502080206, 1) is 4.9997955020802065.
lemma LerpAtOneOvershoots() // @lemma
  ensures Lerp(-3.50468411423970227502877605729736387729644775390625,
               4.9997955020802056225193155114538967609405517578125, 1.0)
          == 4.99979550208020651069773521157912909984588623046875
  ensures Gt(Lerp(-3.50468411423970227502877605729736387729644775390625,
                  4.9997955020802056225193155114538967609405517578125, 1.0),
             4.9997955020802056225193155114538967609405517578125)
{
}

// The B property `a <= lerp(a, b, t) <= b` restricted to small integers,
// where every intermediate is exact.
lemma LerpEndpointsSmallInts(a: fp64, b: fp64) // @lemma
  requires a.IsFinite && b.IsFinite
  requires fp64.LessOrEqual(-1024.0, a) && fp64.LessOrEqual(a, b) && fp64.LessOrEqual(b, 1024.0)
  requires fp64.Equal(fp64.Floor(a), a) && fp64.Equal(fp64.Floor(b), b)
  ensures fp64.Equal(Lerp(a, b, 0.0), a)
  ensures fp64.Equal(Lerp(a, b, 1.0), b)
{
}

// Bridges between fp64 and the int and real views.
predicate IsSafeIntR(x: fp64)
{
  x.IsFinite && (x as real).Floor as real == x as real
  && -9007199254740991.0 <= x as real <= 9007199254740991.0
}

lemma BridgeRoundTrip(i: int) // @lemma
  requires -9007199254740991 <= i <= 9007199254740991
  ensures fp64.FromReal(i as real).IsFinite
  ensures fp64.ToInt(fp64.FromReal(i as real)) == i
{
}

lemma BridgeAdd(x: fp64, y: fp64) // @lemma
  requires IsSafeIntR(x) && IsSafeIntR(y)
  requires -9007199254740991.0 <= x as real + y as real <= 9007199254740991.0
  ensures Add(x, y).IsFinite && Add(x, y) as real == x as real + y as real
{
}
