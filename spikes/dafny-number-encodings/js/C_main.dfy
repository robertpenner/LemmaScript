// -t js smoke test for Encoding C. Compiled together with
// corpus/C_lib.dfy, corpus/C_clamp.dfy and corpus/C_lerp.dfy.
// In JavaScript: clamp(NaN, 0, 10) is NaN, clampNeg(NaN, 0, 10) is 0,
// lerp(1, 3, 0.5) is 2, Infinity + -Infinity is NaN, 1 / -0 is -Infinity.

method Main()
{
  print Clamp(fp64.NaN, 0.0, 10.0), "\n";
  print ClampNeg(fp64.NaN, 0.0, 10.0), "\n";
  print Lerp(1.0, 3.0, 0.5), "\n";
  print Add(fp64.PositiveInfinity, fp64.NegativeInfinity), "\n";
  print Div(1.0, -0.0), "\n";
}
