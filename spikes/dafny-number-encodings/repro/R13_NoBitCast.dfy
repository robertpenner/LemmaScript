// Found during this spike: there is no fp64 <-> bv64 bit-pattern
// conversion. The docs state that `as` between bv and fp types is not
// supported and route through int, which drops NaN payloads and the sign
// of zero. Expected: a resolution error on each `as`.

method ToBits(x: fp64) returns (b: bv64)
{
  b := x as bv64;
}

method FromBits(b: bv64) returns (x: fp64)
{
  x := b as fp64;
}
