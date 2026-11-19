// Workload W4 (bitwise coercions) in Encoding B.
// Library: B_lib.dfy.
//
//   x | 0, x >>> 0, Math.imul(a, b), (a & b), x >>> 3

function OfInt(i: int): Num { Lit(i as real) }

function OrZero(x: Num): Num { OfInt(ToInt32(x)) }

function Ushr0(x: Num): Num { OfInt(ToInt32(x) % TWO32) }

function Imul(a: Num, b: Num): Num
{
  var p := (ToInt32(a) % TWO32) * (ToInt32(b) % TWO32);
  var u := p % TWO32;
  OfInt(if u >= TWO31 then u - TWO32 else u)
}

function And(a: Num, b: Num): Num
{
  var x := ((ToInt32(a) % TWO32) as bv32) & ((ToInt32(b) % TWO32) as bv32);
  var u := x as int;
  OfInt(if u >= TWO31 then u - TWO32 else u)
}

function UshrN(x: Num, n: nat): Num
  requires n < 32
{
  OfInt((((ToInt32(x) % TWO32) as bv32) >> n) as int)
}

lemma OrZeroSpecials() // @lemma
  ensures OrZero(NaN) == PosZero
  ensures OrZero(PosInf) == PosZero
  ensures OrZero(NegZero) == PosZero
  ensures OrZero(Lit(-1.5)) == Lit(-1.0)
  ensures OrZero(Lit(2147483648.0)) == Lit(-2147483648.0)
{
}

lemma OrZeroRange(x: Num) // @lemma
  ensures OrZero(x).Finite? && -(TWO31 as real) <= OrZero(x).r < TWO31 as real
{
}

lemma OrZeroIdempotent(x: Num) // @lemma
  ensures OrZero(OrZero(x)) == OrZero(x)
{
  var i := ToInt32(x); // @manual
  assert TruncReal(i as real) == i; // @manual
}

lemma ImulExamples() // @lemma
  ensures Imul(Lit(65536.0), Lit(65536.0)) == PosZero
  ensures Imul(Lit(-1.0), Lit(8.0)) == Lit(-8.0)
{
}

lemma Ushr0Examples() // @lemma
  ensures Ushr0(Lit(-1.0)) == Lit(4294967295.0)
{
}

lemma AndExample() // @lemma
  ensures And(Lit(-1.0), Lit(255.0)) == Lit(255.0)
{
  assert ToInt32(Lit(-1.0)) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) & (255 as bv32) == 255; // @manual
}

lemma UshrExample() // @lemma
  ensures UshrN(Lit(-1.0), 28) == Lit(15.0)
{
  assert ToInt32(Lit(-1.0)) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) >> 28 == 15; // @manual
}
