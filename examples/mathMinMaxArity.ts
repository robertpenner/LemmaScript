//@ backend dafny

// Math.min / Math.max with one, three, and four positional arguments.
// A unary call returns its argument; longer calls fold left through the
// two-argument helpers. Mixed nat/int operands give an int result, and any
// real operand makes the result real, with integral operands coerced.

export function minOne(a: number): number {
  //@ verify
  //@ ensures \result === a
  return Math.min(a);
}

export function maxOne(a: number): number {
  //@ verify
  //@ ensures \result === a
  return Math.max(a);
}

export function minThree(a: number, b: number, c: number): number {
  //@ verify
  //@ ensures \result <= a && \result <= b && \result <= c
  //@ ensures \result === a || \result === b || \result === c
  return Math.min(a, b, c);
}

export function maxFour(a: number, b: number, c: number, d: number): number {
  //@ verify
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d
  //@ ensures \result === a || \result === b || \result === c || \result === d
  return Math.max(a, b, c, d);
}

export function minLengthOrNegative(xs: number[]): number {
  //@ verify
  //@ ensures \result === -1
  const m = Math.min(xs.length, -1);
  return m;
}

export function minLengthsAndBound(xs: number[], ys: number[], k: number): number {
  //@ verify
  //@ requires k < 0
  //@ ensures \result === k
  const m = Math.min(xs.length, k, ys.length);
  return m;
}

export function maxLengthsAndBounds(xs: number[], ys: number[], lo: number, hi: number): number {
  //@ verify
  //@ ensures \result >= xs.length && \result >= ys.length && \result >= lo && \result >= hi
  return Math.max(xs.length, lo, ys.length, hi);
}

export function minOneReal(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures \result === t
  return Math.min(t);
}

export function maxThreeReal(a: number, b: number, c: number): number {
  //@ verify
  //@ type a real
  //@ type b real
  //@ type c real
  //@ type \result real
  //@ ensures \result >= a && \result >= b && \result >= c
  //@ ensures \result === a || \result === b || \result === c
  return Math.max(a, b, c);
}

export function minMixedFour(n: number, t: number, xs: number[], u: number): number {
  //@ verify
  //@ type t real
  //@ type u real
  //@ type \result real
  //@ ensures \result <= n && \result <= t && \result <= xs.length && \result <= u
  return Math.min(n, t, xs.length, u);
}

export function clampUnitThree(t: number): number {
  //@ verify
  //@ type t real
  //@ type \result real
  //@ ensures 0 <= \result && \result <= 1
  return Math.max(0, Math.min(1, t, 2));
}
