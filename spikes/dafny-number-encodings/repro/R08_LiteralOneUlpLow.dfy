// dafny#6514 "Not in this PR": Boogie's BigFloat.FromBigDec is not
// correctly rounded, so `~1e-5` comes out one ULP low (fixed by
// boogie#1141, which is not in Boogie 3.5.5).
// Correctly rounded 1e-5 as a double:
//   0.000010000000000000000818030539140313095458623138256371021270751953125
// One ULP below it:
//   0.00000999999999999999912396464463171241732197813689708709716796875
// Defect present: OneUlpLow verifies and CorrectlyRounded fails.

lemma CorrectlyRounded()
{
  var x: fp64 := ~0.00001;
  assert x == 0.000010000000000000000818030539140313095458623138256371021270751953125;
}

lemma OneUlpLow()
{
  var x: fp64 := ~0.00001;
  assert x == 0.00000999999999999999912396464463171241732197813689708709716796875;
}
