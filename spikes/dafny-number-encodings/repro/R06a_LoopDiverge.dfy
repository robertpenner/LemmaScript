// dafny#6514 test FpUnsoundLoopAndDivision, first shape (rewritten here):
// Boogie's interval inference is unsound for an fp local reassigned in a
// loop that branches on it.
// Defect present: Diverge verifies `ensures false`.
// Defect absent: the decreases clause fails.

method Diverge() returns (r: int)
  ensures false
{
  var m: fp64 := 0.0;
  r := 0;
  while true
    decreases m
  {
    m := if m == 0.0 then -0.0 else 0.0;
  }
}
