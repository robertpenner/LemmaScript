// -t js smoke test for Encoding B. Compiled together with
// corpus/B_lib.dfy, corpus/B_clamp.dfy and corpus/B_lerp.dfy.
// Expected output: Clamp(NaN, 0, 10) is NaN and ClampNeg(NaN, 0, 10) is
// 0, matching JavaScript; Lerp(1, 3, 1/2) is 2 as an exact real.

method Main()
{
  print Clamp(NaN, Lit(0.0), Lit(10.0)), "\n";
  print ClampNeg(NaN, Lit(0.0), Lit(10.0)), "\n";
  print Lerp(Lit(1.0), Lit(3.0), Lit(0.5)), "\n";
  print Add(PosInf, NegInf), "\n";
  print Div(Lit(1.0), NegZero), "\n";
}
