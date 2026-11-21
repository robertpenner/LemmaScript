// dafny#6514 test FpUnsoundLoopAndDivision, division shapes: the checked
// `/` must reject a -0.0 divisor exactly as it rejects +0.0.
// The dividend is finite and nonzero, so the only check that can fire is
// the zero-divisor check (0/0 would add an invalid-operand check).
// Defect present: ByPosZero reports a division-by-zero error but
// ByNegZero verifies.

method ByNegZero(x: fp64) returns (r: fp64)
  requires x.IsFinite && !x.IsZero
{
  var z: fp64 := -0.0;
  r := x / z;
}

method ByPosZero(x: fp64) returns (r: fp64)
  requires x.IsFinite && !x.IsZero
{
  var z: fp64 := 0.0;
  r := x / z;
}
