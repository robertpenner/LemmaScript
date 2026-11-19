// dafny#6514, verifier defect 2: fp32.E was 11398091/2^22, 3209 ULP below
// the nearest binary32 to e, which is 11401300/2^22 = 2.71828174591064453125.
// Defect present: Buggy verifies and Correct fails (or times out).

lemma Buggy()
{
  assert fp32.E as real == 11398091.0 / 4194304.0;
}

lemma Correct()
{
  assert fp32.E as real == 2.71828174591064453125;
}
