export function f(x: number, y: number): number {
  //@ type x real
  //@ type y real
  //@ type \result real
  return Math.min(x, y);
}
