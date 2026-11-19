// dafny#6514 test FpUnsoundLoopAndDivision, division shapes: the checked
// `/` must reject a -0.0 divisor exactly as it rejects +0.0.
// Defect present: ByPosZero reports a division-by-zero error but
// ByNegZero does not.

method ByNegZero(x: fp64) returns (r: fp64)
  requires !x.IsNaN
{
  var z: fp64 := -0.0;
  r := x / z;
}

method ByPosZero(x: fp64) returns (r: fp64)
  requires !x.IsNaN
{
  var z: fp64 := 0.0;
  r := x / z;
}
