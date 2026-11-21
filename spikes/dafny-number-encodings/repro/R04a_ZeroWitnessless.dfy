// dafny#6514, verifier defect 4: Zero() built an fp literal without its
// resolved value. A witness-less subset type asks for a default value.
// Defect present: the translator crashes. Defect absent: it verifies or
// reports an ordinary witness error.

type NonNaN = x: fp64 | !x.IsNaN

method UseNonNaN(a: NonNaN)
{
  var x := a;
}
