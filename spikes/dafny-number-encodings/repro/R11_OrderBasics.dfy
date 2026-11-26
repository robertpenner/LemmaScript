// Found during this spike: trichotomy and transitivity of the unchecked
// IEEE comparisons, the facts every clamp or search proof needs.

lemma Trichotomy(x: fp64, y: fp64)
  requires !x.IsNaN && !y.IsNaN
  ensures !fp64.Less(x, y) ==> fp64.LessOrEqual(y, x)
{
}

lemma Transitivity(x: fp64, y: fp64, z: fp64)
  requires fp64.LessOrEqual(x, y) && fp64.LessOrEqual(y, z)
  ensures fp64.LessOrEqual(x, z)
{
}

lemma NotGreaterThanFiniteIsFinite(x: fp64, hi: fp64)
  requires hi.IsFinite && !x.IsNaN && !fp64.Greater(x, hi) && fp64.LessOrEqual(0.0, x)
  ensures x.IsFinite
{
}
