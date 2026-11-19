/**
 * Number.isSafeInteger on real, integral, and non-numeric operands.
 *
 * JavaScript's `Number.isSafeInteger(x)` is true exactly when `x` is a number
 * with no fractional part and |x| <= 2^53 - 1. A `real` operand (bare `/`, a
 * fractional literal, or a `//@ type x real` variable) lowers to the preamble
 * predicate `IsSafeIntegerReal`, which checks integrality and the safe range
 * while evaluating its argument once. Integral operands keep the plain range
 * check; a `string` is never a number, so the call is `false`.
 */

//@ backend dafny

export function isSafeReal(x: number): boolean {
  //@ type x real
  return Number.isSafeInteger(x);
}

// A compound real argument is passed to the predicate once.
export function isSafeQuotient(a: number, b: number): boolean {
  //@ requires b !== 0
  //@ ensures \result === isSafeReal(a / b)
  return Number.isSafeInteger(a / b);
}

export function isSafeInt(n: number): boolean {
  return Number.isSafeInteger(n);
}

export function isSafeText(s: string): boolean {
  //@ ensures \result === false
  return Number.isSafeInteger(s);
}

// Exact integral reals within the safe range.
export function integralRealsAreSafe(): boolean {
  //@ ensures \result === true
  return Number.isSafeInteger(4 / 2) && Number.isSafeInteger(-4 / 2) &&
    isSafeReal(0) && isSafeReal(9007199254740991) && isSafeReal(-9007199254740991);
}

// Fractional reals and exact reals just outside the safe range.
export function unsafeReals(): boolean {
  //@ ensures \result === false
  return Number.isSafeInteger(3 / 2) || Number.isSafeInteger(-0.5) ||
    isSafeReal(9007199254740992) || isSafeReal(-9007199254740992);
}

// The integral bound is unchanged: 2^53 - 1 is safe, 2^53 is not.
export function integralBounds(): boolean {
  //@ ensures \result === true
  return isSafeInt(9007199254740991) && isSafeInt(-9007199254740991) &&
    !isSafeInt(9007199254740992) && !isSafeInt(-9007199254740992);
}
