// dafny#6514 test FpUnsoundLoopAndDivision, second shape (rewritten here):
// same defect without an fp decreases clause. After 11 toggles m is -0.0,
// so the assertion is false.
// Defect present: OddCount verifies. Defect absent: the assertion fails.

method OddCount()
{
  var m: fp64 := 0.0;
  var i := 0;
  while i < 11
    decreases 11 - i
  {
    m := if m == 0.0 then -0.0 else 0.0;
    i := i + 1;
  }
  assert m == 0.0;
}
