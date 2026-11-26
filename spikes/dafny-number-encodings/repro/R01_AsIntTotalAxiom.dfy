// dafny#6514, verifier defect 1: `x as int` went through fp.to_sbv with a
// total axiom that kept the result in [-2^63, 2^63).
// 1e20 is an exact binary64 value (2^20 * 5^20, and 5^20 < 2^53).
// Defect present: TooSmall verifies, so together with Exact the verifier
// accepts two contradictory facts. Defect absent: TooSmall fails.

lemma Exact()
{
  var x: fp64 := 100000000000000000000.0;
  assert (x as int) == 100000000000000000000;
}

lemma TooSmall()
{
  var x: fp64 := 100000000000000000000.0;
  assert (x as int) < 9223372036854775808;
}

lemma ToIntTooSmall()
{
  var x: fp64 := 100000000000000000000.0;
  assert fp64.ToInt(x) < 9223372036854775808;
}

lemma ToIntExact()
{
  var x: fp64 := 100000000000000000000.0;
  assert fp64.ToInt(x) == 100000000000000000000;
}
