export function f(xs: number[]): number {
  //@ requires xs.length > 0
  return Math.max(...xs);
}
