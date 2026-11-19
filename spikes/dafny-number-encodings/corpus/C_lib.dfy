// Encoding C: native IEEE binary64 (fp64) on a Dafny nightly that includes
// dafny-lang/dafny#6323. Not available in pinned Dafny 4.11.0.
//
// JavaScript operators are wrapped in Dafny's unchecked static methods
// (fp64.Add, fp64.Equal, fp64.Less, ...), which follow IEEE 754 and carry no
// well-formedness obligations. The checked operators (+, <, ==) would add a
// "not NaN" obligation at every use, which JavaScript does not have.

// A synonym `type F = fp64` would be shorter, but assigning a literal to
// it crashes the nightly translator (see repro/R10_SynonymLiteralCrash.dfy).

function Add(x: fp64, y: fp64): fp64 { fp64.Add(x, y) }
function Sub(x: fp64, y: fp64): fp64 { fp64.Sub(x, y) }
function Mul(x: fp64, y: fp64): fp64 { fp64.Mul(x, y) }
function Div(x: fp64, y: fp64): fp64 { fp64.Div(x, y) }
function Neg(x: fp64): fp64 { fp64.Neg(x) }

predicate StrictEq(x: fp64, y: fp64) { fp64.Equal(x, y) }
predicate Lt(x: fp64, y: fp64) { fp64.Less(x, y) }
predicate Le(x: fp64, y: fp64) { fp64.LessOrEqual(x, y) }
predicate Gt(x: fp64, y: fp64) { fp64.Greater(x, y) }
predicate Ge(x: fp64, y: fp64) { fp64.GreaterOrEqual(x, y) }

// Object.is, written without ghost `==` so it is usable in compiled code.
predicate ObjectIs(x: fp64, y: fp64)
{
  (x.IsNaN && y.IsNaN)
  || (!x.IsNaN && !y.IsNaN && fp64.Equal(x, y) && (x.IsZero ==> x.IsNegative == y.IsNegative))
}

predicate SameValueZero(x: fp64, y: fp64) { fp64.Equal(x, y) || (x.IsNaN && y.IsNaN) }

predicate Truthy(x: fp64) { !x.IsNaN && !x.IsZero }

function MathMin(x: fp64, y: fp64): fp64
{
  if x.IsNaN || y.IsNaN then fp64.NaN
  else if x.IsZero && y.IsZero then (if x.IsNegative then x else y)
  else if fp64.Less(y, x) then y else x
}

function MathMax(x: fp64, y: fp64): fp64
{
  if x.IsNaN || y.IsNaN then fp64.NaN
  else if x.IsZero && y.IsZero then (if x.IsNegative then y else x)
  else if fp64.Less(x, y) then y else x
}

// Math.trunc: Floor for non-negative, Ceiling for negative. Ceiling of a
// value in (-1, 0) is -0 under IEEE rounding, matching JavaScript.
function MathTrunc(x: fp64): fp64
{
  if x.IsNaN then x
  else if x.IsNegative then fp64.Ceiling(x)
  else fp64.Floor(x)
}

// Math.round: round half toward +Infinity. Floor(x + 0.5) is wrong for
// 0.49999999999999994 (x + 0.5 rounds up to 1.0), so the JS algorithm
// compares the distance to Floor(x) instead.
function MathRound(x: fp64): fp64
{
  if x.IsNaN || x.IsInfinite || x.IsZero then x
  else
    var f := fp64.Floor(x);
    var r := if fp64.GreaterOrEqual(fp64.Sub(x, f), 0.5) then fp64.Add(f, 1.0) else f;
    if r.IsZero && x.IsNegative then fp64.Neg(0.0) else r
}

const TWO32: int := 4294967296
const TWO31: int := 2147483648

function ToInt32(x: fp64): int
{
  if !x.IsFinite then 0
  else
    var u := fp64.ToInt(x) % TWO32;
    if u >= TWO31 then u - TWO32 else u
}
