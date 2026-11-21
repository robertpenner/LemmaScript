// Minimal -t js probe for fp64 with no companion-type member access
// (no fp64.NaN, no fp64.Add). Separates the code generator crash that
// js/C_main.dfy hits from what the JS backend does with plain fp64
// arithmetic. In JavaScript the expected lines are:
//   3.5
//   0.30000000000000004
//   false
//   0.3333333333333333

method Main()
{
  var x: fp64 := 1.5;
  var y: fp64 := 2.0;
  print x + y, "\n";
  var a: fp64 := ~0.1;
  var b: fp64 := ~0.2;
  var c: fp64 := ~0.3;
  print a + b, "\n";
  print a + b == c, "\n";
  var one: fp64 := 1.0;
  var three: fp64 := 3.0;
  print one / three, "\n";
}
