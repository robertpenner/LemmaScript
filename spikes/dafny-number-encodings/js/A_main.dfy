// -t js smoke test for Encoding A. Compiled together with
// corpus/A_lib.dfy, corpus/A_safeint.dfy and corpus/A_clamp.dfy.
// Expected output: 7, 7, 2, 0, 5, 10.

method Main()
{
  print Midpoint(4, 10), "\n";
  print MidpointNaive(4, 10), "\n";
  var idx := BinarySearch([1, 3, 5, 7], 5);
  print idx, "\n";
  print Clamp(-3, 0, 10), "\n";
  print Clamp(5, 0, 10), "\n";
  print Clamp(42, 0, 10), "\n";
}
