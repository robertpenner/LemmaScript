//@ backend dafny

// Math.max / Math.min with spread arguments over real sequences. When any
// segment is real, integral segments and positional arguments are coerced
// and the aggregate uses the real MaxOfSeqReal / MinOfSeqReal helpers.

export function highReal(xs: number[]): number {
  //@ verify
  //@ type xs real[]
  //@ type \result real
  //@ requires xs.length > 0
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  return Math.max(...xs);
}

export function lowReal(xs: number[]): number {
  //@ verify
  //@ type xs real[]
  //@ type \result real
  //@ requires xs.length > 0
  //@ ensures forall(i: nat, i < xs.length ==> \result <= xs[i])
  return Math.min(...xs);
}

export function highRealOrZero(xs: number[]): number {
  //@ verify
  //@ type xs real[]
  //@ type \result real
  //@ ensures \result >= 0
  //@ ensures forall(i: nat, i < xs.length ==> xs[i] <= \result)
  return Math.max(0, ...xs);
}

export function lowRealBounded(n: number, xs: number[], t: number): number {
  //@ verify
  //@ type xs real[]
  //@ type t real
  //@ type \result real
  //@ ensures \result <= n && \result <= t
  //@ ensures forall(i: nat, i < xs.length ==> \result <= xs[i])
  return Math.min(n, ...xs, t);
}

export function highMixedSeqs(ints: number[], reals: number[]): number {
  //@ verify
  //@ type reals real[]
  //@ type \result real
  //@ requires ints.length + reals.length > 0
  //@ ensures forall(i: nat, i < ints.length ==> ints[i] <= \result)
  //@ ensures forall(i: nat, i < reals.length ==> reals[i] <= \result)
  return Math.max(...ints, ...reals);
}
