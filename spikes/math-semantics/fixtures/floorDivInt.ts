export function f(x: number, y: number): number {
  //@ requires y !== 0
  return Math.floor(x / y);
}
