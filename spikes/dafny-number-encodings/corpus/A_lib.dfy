// Encoding A: checked safe-integer abstraction on pinned Dafny 4.11.0.
// A JavaScript number is admitted only when it is an integer in
// [-(2^53 - 1), 2^53 - 1]. Every arithmetic result must be proved to stay in
// that range. NaN, infinities, fractions, and -0 cannot be represented.
//
// Proof-hint convention for the whole corpus: a line ending in `// @manual`
// is a hand-written assertion, lemma call, or extra invariant that exists only
// to help the verifier. A lemma declaration line ends in `// @helper` when
// another proof calls the lemma (a hand-written hint) and in `// @target`
// when the lemma is a workload statement. run.sh counts the three tags per
// file, matching only tags at the end of a line.

const MAX_SAFE: int := 9007199254740991
const TWO32: int := 4294967296
const TWO31: int := 2147483648

newtype SafeInt = x: int | -9007199254740991 <= x <= 9007199254740991

predicate IsSafe(x: int) { -MAX_SAFE <= x <= MAX_SAFE }

function Abs(x: int): int { if x < 0 then -x else x }

// JS `n % d` on safe integers. The sign follows the dividend. `d == 0` gives
// NaN in JS, which is outside SafeInt, so it is a precondition here.
function JSRem(n: int, d: int): int
  requires d != 0
{
  var r := Abs(n) % Abs(d);
  if n >= 0 then r else -r
}

// JS `Math.trunc(n / d)` on safe integers.
function JSTruncDiv(n: int, d: int): int
  requires d != 0
{
  var q := Abs(n) / Abs(d);
  if (n >= 0) == (d > 0) then q else -q
}

// ECMAScript ToUint32 / ToInt32 restricted to integers.
function ToUint32(x: int): int { x % TWO32 }

function ToInt32(x: int): int
{
  var u := ToUint32(x);
  if u >= TWO31 then u - TWO32 else u
}

function Sum(a: seq<int>): int
{
  if |a| == 0 then 0 else Sum(a[..|a| - 1]) + a[|a| - 1]
}
