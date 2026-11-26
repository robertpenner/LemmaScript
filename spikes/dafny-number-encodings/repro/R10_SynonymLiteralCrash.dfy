// Found during this spike (not listed by case in dafny#6514, which
// mentions "six translation crashes" and synonym handling): assigning an
// fp literal to a type synonym of fp64 crashes the nightly with
// System.ArgumentException "Not a float type: F".

type F = fp64

method M()
{
  var x: F := 0.0;
}
