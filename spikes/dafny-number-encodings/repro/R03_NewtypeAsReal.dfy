// dafny#6514, verifier defect 3: `as real` on a newtype over fp64 skipped
// the finiteness obligation, so the translation's `else 0.0` branch made a
// false statement provable.
// Defect present: Bad verifies with no errors. Defect absent: Bad reports
// a missing finiteness obligation.

newtype MyF = fp64

lemma Bad(x: MyF)
  requires (x as fp64).IsInfinite
{
  assert (x as real) == 0.0;
}
