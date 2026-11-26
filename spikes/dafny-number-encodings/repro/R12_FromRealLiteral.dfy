// Found during this spike: fp64.FromReal on a real literal, and ToInt on
// a literal, which the bitwise workload depends on.

lemma FromRealZero() ensures fp64.FromReal(0.0) == 0.0 {}
lemma FromRealOne() ensures fp64.FromReal(1.0) == 1.0 {}
lemma ToIntNegOne() ensures fp64.ToInt(-1.0) == -1 {}
lemma NaNIsUnique(x: fp64) requires x.IsNaN ensures x == fp64.NaN {}
