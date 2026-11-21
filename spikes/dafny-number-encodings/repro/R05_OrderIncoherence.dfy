// dafny#6514 incoherence: ghost `==` is identity (+0 != -0) while `<` and
// `<=` were raw IEEE comparisons (+0 <= -0 and -0 <= +0 both hold).
// Defect present: Antisymmetry fails with a counterexample at the signed
// zeros, and SignedZeroWitness verifies.

lemma Antisymmetry(a: fp64, b: fp64)
  requires !a.IsNaN && !b.IsNaN
  ensures a <= b && b <= a ==> a == b
{
}

lemma SignedZeroWitness()
{
  var p: fp64 := 0.0;
  var n: fp64 := -0.0;
  assert p <= n && n <= p && p != n;
}
