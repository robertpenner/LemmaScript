// Workload W4 (bitwise coercions) in Encoding C.
// Library: C_lib.dfy.
//
//   x | 0, x >>> 0, Math.imul(a, b), (a & b), x >>> 3
//
// Dafny has no fp64 <-> bv conversion, so every bitwise operator goes
// fp64 -> int (fp64.ToInt) -> bv32 -> int -> fp64 (fp64.FromReal).

function OfInt(i: int): fp64 { fp64.FromReal(i as real) }

function OrZero(x: fp64): fp64 { OfInt(ToInt32(x)) }

function Ushr0(x: fp64): fp64 { OfInt(ToInt32(x) % TWO32) }

function Imul(a: fp64, b: fp64): fp64
{
  var p := (ToInt32(a) % TWO32) * (ToInt32(b) % TWO32);
  var u := p % TWO32;
  OfInt(if u >= TWO31 then u - TWO32 else u)
}

function And(a: fp64, b: fp64): fp64
{
  var x := ((ToInt32(a) % TWO32) as bv32) & ((ToInt32(b) % TWO32) as bv32);
  var u := x as int;
  OfInt(if u >= TWO31 then u - TWO32 else u)
}

function UshrN(x: fp64, n: nat): fp64
  requires n < 32
{
  OfInt((((ToInt32(x) % TWO32) as bv32) >> n) as int)
}

lemma OrZeroSpecials() // @lemma
  ensures OrZero(fp64.NaN) == 0.0
  ensures OrZero(fp64.PositiveInfinity) == 0.0
  ensures OrZero(fp64.Neg(0.0)) == 0.0
  ensures OrZero(-1.5) == -1.0
  ensures OrZero(2147483648.0) == -2147483648.0
{
}

lemma OrZeroRange(x: fp64) // @lemma
  ensures OrZero(x).IsFinite
  ensures -2147483648.0 <= OrZero(x) as real < 2147483648.0
{
}

lemma OrZeroIdempotent(x: fp64) // @lemma
  ensures OrZero(OrZero(x)) == OrZero(x)
{
}

lemma ImulExamples() // @lemma
  ensures Imul(65536.0, 65536.0) == 0.0
  ensures Imul(-1.0, 8.0) == -8.0
{
}

lemma Ushr0Examples() // @lemma
  ensures Ushr0(-1.0) == 4294967295.0
{
}

lemma AndExample() // @lemma
  ensures And(-1.0, 255.0) == 255.0
{
  assert ToInt32(-1.0) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) & (255 as bv32) == 255; // @manual
}

lemma UshrExample() // @lemma
  ensures UshrN(-1.0, 28) == 15.0
{
  assert ToInt32(-1.0) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) >> 28 == 15; // @manual
}
