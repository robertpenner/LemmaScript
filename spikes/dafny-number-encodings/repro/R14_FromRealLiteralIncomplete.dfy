// Found during this spike: probing fp64.FromReal on a real literal.
// NegZero and Pos state false claims; IsZero, NotNegative, One and IntCast
// state true ones. If none of the first five verifies, the verifier is
// incomplete here but not unsound. IntCast is the contrast: the same value
// written as `0 as real`.

lemma NegZero() ensures fp64.FromReal(0.0) == fp64.Neg(0.0) {}
lemma IsZero() ensures fp64.FromReal(0.0).IsZero {}
lemma NotNegative() ensures !fp64.FromReal(0.0).IsNegative {}
lemma Pos() ensures fp64.FromReal(0.0) != 0.0 {}
lemma One() ensures fp64.FromReal(1.0) == 1.0 {}
lemma IntCast() ensures fp64.FromReal(0 as real) == 0.0 {}
