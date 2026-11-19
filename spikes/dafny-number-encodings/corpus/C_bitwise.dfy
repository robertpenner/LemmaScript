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

lemma OrZeroSpecials() // @target
  ensures OrZero(fp64.NaN) == 0.0
  ensures OrZero(fp64.PositiveInfinity) == 0.0
  ensures OrZero(fp64.Neg(0.0)) == 0.0
  ensures OrZero(-1.5) == -1.0
  ensures OrZero(2147483648.0) == -2147483648.0
{
}

lemma OrZeroRange(x: fp64) // @target
  ensures OrZero(x).IsFinite
  ensures -2147483648.0 <= OrZero(x) as real < 2147483648.0
{
}

lemma OrZeroIdempotent(x: fp64) // @target
  ensures OrZero(OrZero(x)) == OrZero(x)
{
}

lemma ImulExamples() // @target
  ensures Imul(65536.0, 65536.0) == 0.0
  ensures Imul(-1.0, 8.0) == -8.0
{
}

lemma Ushr0Examples() // @target
  ensures Ushr0(-1.0) == 4294967295.0
{
}

lemma AndExample() // @target
  ensures And(-1.0, 255.0) == 255.0
{
  assert ToInt32(-1.0) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) & (255 as bv32) == 255; // @manual
}

lemma UshrExample() // @target
  ensures UshrN(-1.0, 28) == 15.0
{
  assert ToInt32(-1.0) % TWO32 == 4294967295; // @manual
  assert (4294967295 as bv32) >> 28 == 15; // @manual
}

// The symbolic statements A_bitwise.dfy proves, restated over fp64. A cannot
// represent -0, so OrZeroOnInt32 excludes it here.
lemma OrZeroOnInt32(x: fp64) // @target
  requires x.IsFinite && !(x.IsZero && x.IsNegative)
  requires (x as real).Floor as real == x as real
  requires -2147483648.0 <= x as real < 2147483648.0
  ensures OrZero(x) == x
{
}

lemma ImulSmall(a: fp64, b: fp64) // @target
  requires a.IsFinite && (a as real).Floor as real == a as real && 0.0 <= a as real < 65536.0
  requires b.IsFinite && (b as real).Floor as real == b as real && 0.0 <= b as real < 32768.0
  ensures Imul(a, b).IsFinite && Imul(a, b) as real == (a as real) * (b as real)
{
  assert ToInt32(a) == (a as real).Floor; // @manual
  assert ToInt32(b) == (b as real).Floor; // @manual
  MulBound(ToInt32(a), 65535, ToInt32(b), 32767); // @manual
}

lemma MulBound(x: int, xm: int, y: int, ym: int) // @helper
  requires 0 <= x <= xm && 0 <= y <= ym
  ensures x * y <= xm * ym
{
  assert x * y <= xm * y; // @manual
}

lemma AndWithSelf(a: fp64) // @target
  ensures And(a, a) == OrZero(a)
{
  var u := (ToInt32(a) % TWO32) as bv32; // @manual
  assert u & u == u; // @manual
  Bv32RoundTrip(ToInt32(a) % TWO32); // @manual
}

lemma Bv32RoundTrip(x: int) // @helper
  requires 0 <= x < TWO32
  ensures (x as bv32) as int == x
{
}
