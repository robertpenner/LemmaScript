// Workload W4 (bitwise coercions) in Encoding A.
// Library: A_lib.dfy.
//
//   x | 0, x >>> 0, Math.imul(a, b), (a & b), x >>> 3
//
// Bit operations are modeled as int arithmetic modulo 2^32, with bv32 used
// only where an operator has no arithmetic form (`&`).

function OrZero(x: SafeInt): (r: SafeInt)
  ensures -TWO31 <= r as int < TWO31
{
  ToInt32(x as int) as SafeInt
}

function Ushr0(x: SafeInt): (r: SafeInt)
  ensures 0 <= r as int < TWO32
{
  ToUint32(x as int) as SafeInt
}

function Imul(a: SafeInt, b: SafeInt): (r: SafeInt)
  ensures -TWO31 <= r as int < TWO31
{
  ToInt32(ToUint32(a as int) * ToUint32(b as int)) as SafeInt
}

function And(a: SafeInt, b: SafeInt): (r: SafeInt)
  ensures -TWO31 <= r as int < TWO31
{
  var x := (ToUint32(a as int) as bv32) & (ToUint32(b as int) as bv32);
  ToInt32(x as int) as SafeInt
}

function UshrN(x: SafeInt, n: nat): (r: SafeInt)
  requires n < 32
  ensures 0 <= r as int < TWO32
{
  ((ToUint32(x as int) as bv32) >> n) as int as SafeInt
}

lemma OrZeroIdempotent(x: SafeInt) // @target
  ensures OrZero(OrZero(x)) == OrZero(x)
{
}

lemma OrZeroOnInt32(x: SafeInt) // @target
  requires -TWO31 <= x as int < TWO31
  ensures OrZero(x) == x
{
}

lemma ImulSmall(a: SafeInt, b: SafeInt) // @target
  requires 0 <= a < 65536 && 0 <= b < 32768
  ensures Imul(a, b) as int == a as int * b as int
{
  MulBound(a as int, 65535, b as int, 32767); // @manual
}

lemma MulBound(x: int, xm: int, y: int, ym: int) // @helper
  requires 0 <= x <= xm && 0 <= y <= ym
  ensures x * y <= xm * ym
{
  assert x * y <= xm * y; // @manual
}

lemma AndWithSelf(a: SafeInt) // @target
  ensures And(a, a) == OrZero(a)
{
  var u := ToUint32(a as int) as bv32; // @manual
  assert u & u == u; // @manual
  Bv32RoundTrip(ToUint32(a as int)); // @manual
}

// The int -> bv32 -> int round trip on a symbolic value. With the pinned
// toolchain this lemma times out at 30 s; AndWithSelf depends on it.
lemma Bv32RoundTrip(x: int) // @helper
  requires 0 <= x < TWO32
  ensures (x as bv32) as int == x
{
}

method Examples()
{
  assert OrZero(2147483648) == -2147483648;
  assert Ushr0(-1) == 4294967295;
  assert Imul(65536, 65536) == 0;
  assert Imul(-1, 8) == -8;
  assert ToUint32(-1) == 4294967295; // @manual
  assert (4294967295 as bv32) & (255 as bv32) == 255; // @manual
  assert And(-1, 255) == 255;
  assert (4294967295 as bv32) >> 28 == 15; // @manual
  assert UshrN(-1, 28) == 15;
}
