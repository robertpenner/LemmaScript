// Encoding B: algebraic extended real on pinned Dafny 4.11.0.
// A JavaScript number is an exact real payload plus the IEEE special values
// (NaN, +Infinity, -Infinity, -0). Arithmetic is exact: there is no rounding
// and no overflow to infinity. This is a deliberate approximation of IEEE
// binary64; the corpus records where it diverges from JavaScript.

datatype NumRaw = Finite(r: real, negZero: bool) | PosInf | NegInf | NaN

type Num = n: NumRaw | n.Finite? ==> (n.negZero ==> n.r == 0.0)
  witness NaN

const PosZero: Num := Finite(0.0, false)
const NegZero: Num := Finite(0.0, true)

function Lit(r: real): Num { Finite(r, false) }

predicate IsNaN(x: Num) { x.NaN? }
predicate IsZero(x: Num) { x.Finite? && x.r == 0.0 }
predicate IsFinite(x: Num) { x.Finite? }

// Sign bit as JavaScript observes it (1 / x < 0 for -0).
predicate SignNeg(x: Num)
{
  match x
  case Finite(r, nz) => r < 0.0 || nz
  case NegInf => true
  case _ => false
}

function Neg(x: Num): Num
{
  match x
  case Finite(r, nz) => if r == 0.0 then Finite(0.0, !nz) else Finite(-r, false)
  case PosInf => NegInf
  case NegInf => PosInf
  case NaN => NaN
}

function Add(x: Num, y: Num): Num
{
  match (x, y)
  case (NaN, _) => NaN
  case (_, NaN) => NaN
  case (PosInf, NegInf) => NaN
  case (NegInf, PosInf) => NaN
  case (PosInf, _) => PosInf
  case (NegInf, _) => NegInf
  case (_, PosInf) => PosInf
  case (_, NegInf) => NegInf
  case (Finite(a, na), Finite(b, nb)) =>
    if a + b == 0.0 then Finite(0.0, a == 0.0 && b == 0.0 && na && nb)
    else Finite(a + b, false)
}

function Sub(x: Num, y: Num): Num { Add(x, Neg(y)) }

function InfOf(neg: bool): Num { if neg then NegInf else PosInf }

function Mul(x: Num, y: Num): Num
{
  if x.NaN? || y.NaN? then NaN
  else
    var neg := SignNeg(x) != SignNeg(y);
    if (!x.Finite? && IsZero(y)) || (!y.Finite? && IsZero(x)) then NaN
    else if !x.Finite? || !y.Finite? then InfOf(neg)
    else if x.r * y.r == 0.0 then Finite(0.0, neg)
    else Finite(x.r * y.r, false)
}

function Div(x: Num, y: Num): Num
{
  if x.NaN? || y.NaN? then NaN
  else
    var neg := SignNeg(x) != SignNeg(y);
    if !x.Finite? && !y.Finite? then NaN
    else if !x.Finite? then InfOf(neg)
    else if !y.Finite? then Finite(0.0, neg)
    else if y.r == 0.0 then (if x.r == 0.0 then NaN else InfOf(neg))
    else if x.r / y.r == 0.0 then Finite(0.0, neg)
    else Finite(x.r / y.r, false)
}

function TruncReal(r: real): int
{
  if r >= 0.0 then r.Floor else -((-r).Floor)
}

// JS `%`: result has the dividend's sign.
function Rem(x: Num, y: Num): Num
{
  if x.NaN? || y.NaN? || !x.Finite? || IsZero(y) then NaN
  else if !y.Finite? then x
  else
    var q := TruncReal(x.r / y.r);
    var m := x.r - y.r * (q as real);
    if m == 0.0 then Finite(0.0, SignNeg(x)) else Finite(m, false)
}

// Comparisons are false whenever either side is NaN; -0 equals +0.
predicate Lt(x: Num, y: Num)
{
  match (x, y)
  case (NaN, _) => false
  case (_, NaN) => false
  case (NegInf, NegInf) => false
  case (NegInf, _) => true
  case (_, PosInf) => !x.PosInf?
  case (PosInf, _) => false
  case (_, NegInf) => false
  case (Finite(a, _), Finite(b, _)) => a < b
}

predicate StrictEq(x: Num, y: Num)
{
  match (x, y)
  case (NaN, _) => false
  case (_, NaN) => false
  case (Finite(a, _), Finite(b, _)) => a == b
  case _ => x == y
}

predicate Le(x: Num, y: Num) { Lt(x, y) || StrictEq(x, y) }
predicate Gt(x: Num, y: Num) { Lt(y, x) }
predicate Ge(x: Num, y: Num) { Le(y, x) }

predicate ObjectIs(x: Num, y: Num) { x == y }
predicate SameValueZero(x: Num, y: Num) { StrictEq(x, y) || (x.NaN? && y.NaN?) }

predicate Truthy(x: Num) { !x.NaN? && !IsZero(x) }

// Math.min / Math.max: NaN if either is NaN; -0 is smaller than +0.
function MathMin(x: Num, y: Num): Num
{
  if x.NaN? || y.NaN? then NaN
  else if IsZero(x) && IsZero(y) then Finite(0.0, x.negZero || y.negZero)
  else if Lt(y, x) then y else x
}

function MathMax(x: Num, y: Num): Num
{
  if x.NaN? || y.NaN? then NaN
  else if IsZero(x) && IsZero(y) then Finite(0.0, x.negZero && y.negZero)
  else if Lt(x, y) then y else x
}

function MathTrunc(x: Num): Num
{
  if !x.Finite? then x
  else
    var t := TruncReal(x.r) as real;
    if t == 0.0 then Finite(0.0, SignNeg(x)) else Finite(t, false)
}

// Math.round: floor(r + 0.5), with -0 for results in [-0.5, 0).
function MathRound(x: Num): Num
{
  if !x.Finite? then x
  else
    var t := (x.r + 0.5).Floor as real;
    if t == 0.0 then Finite(0.0, SignNeg(x)) else Finite(t, false)
}

const TWO32: int := 4294967296
const TWO31: int := 2147483648

// ToInt32 for the integer-valued subset of payloads after truncation.
function ToInt32(x: Num): int
{
  if !x.Finite? then 0
  else
    var u := TruncReal(x.r) % TWO32;
    if u >= TWO31 then u - TWO32 else u
}
