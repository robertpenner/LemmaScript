// dafny#6514, verifier defect 4, second shape: assign-such-that on fp64.
// Defect present: the translator crashes.

method Pick(v: fp64)
{
  var e: fp64 :| e == v;
}
