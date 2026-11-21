// -t js probe: a single companion-type constant, fp64.NaN.
// js/C_main.dfy crashes the JS code generator; this isolates whether
// member access on the fp64 companion type alone triggers it.

method Main()
{
  var n: fp64 := fp64.NaN;
  print n.IsNaN, "\n";
}
