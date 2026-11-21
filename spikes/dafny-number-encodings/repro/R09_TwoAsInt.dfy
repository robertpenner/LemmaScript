// dafny#6514 "Not in this PR": `as int` and `as real` go through
// fp.to_real, which Z3 handles poorly. The PR reports that
// `2.0 as fp64 as int` times out.

lemma TwoAsInt()
{
  assert 2.0 as fp64 as int == 2;
}

lemma TwoAsReal()
{
  assert 2.0 as fp64 as real == 2.0;
}
