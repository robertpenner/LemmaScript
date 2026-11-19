import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract";
import { resolveModule } from "../src/resolve";
import { narrowModule } from "../src/narrow";
import { transformModuleDafny, transformModuleLean } from "../src/transform";
import { emitDafnyFile } from "../src/dafny-emit";
import { emitLeanFile, resetLeanModule } from "../src/lean-emit";

const source = `
export function isSafe(n: number): boolean {
  return Number.isSafeInteger(n);
}
export function isSafeBig(b: bigint): boolean {
  return Number.isSafeInteger(b);
}
`;

function sourceModule(text = source, typeChecked = true) {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("safe.ts", text);
  if (typeChecked) assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-safe-integer-"));
  try {
    const proof = join(dir, "safe.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", proof],
      { encoding: "utf8", timeout: 120_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// JavaScript: Number.isSafeInteger(2 ** 53 - 1) === true, (2 ** 53) === false,
// and symmetrically for the negatives. LemmaScript models `number` as an
// unbounded integer, so the bound must appear explicitly in the lowering.
// A bigint is not a number, so Number.isSafeInteger(5n) === false.
const facts = `
lemma SafeIntegerBounds()
  ensures isSafe(9007199254740991) && isSafe(-9007199254740991) && isSafe(0)
  ensures !isSafe(9007199254740992) && !isSafe(-9007199254740992)
  ensures !isSafeBig(0) && !isSafeBig(5)
{}
`;

test("Dafny lowers Number.isSafeInteger to the 2^53 - 1 bound", () => {
  const { typesFile, defFile } = transformModuleDafny(sourceModule());
  const output = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "safe.ts");
  assert.doesNotMatch(output, /isSafeInteger/, output);
  const ok = verify(output + facts);
  assert.equal(ok.status, 0, ok.output);
  for (const claim of ["isSafe(9007199254740992)", "isSafeBig(5)"]) {
    const wrong = verify(output + `\nlemma Wrong() ensures ${claim} {}\n`);
    assert.notEqual(wrong.status, 0, wrong.output);
    assert.match(wrong.output, /could not be proved|might not hold/);
  }
});

test("Lean lowers Number.isSafeInteger to the 2^53 - 1 bound", () => {
  const { typesFile, defFile } = transformModuleLean(sourceModule());
  resetLeanModule();
  const output = emitLeanFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] });
  assert.doesNotMatch(output, /isSafeInteger/, output);
  assert.match(output, /-9007199254740991 ≤ n ∧ n ≤ 9007199254740991/, output);
  assert.match(output, /def isSafeBig[^\n]*\n(?:[^\n]*\n)*?\s*false\b/, output);
});

// A value that may hold a number at runtime cannot fold to false: with
// x = 3, Number.isSafeInteger(x) is true. Such calls, and calls with the wrong
// arity, must fail instead of emitting a raw Number.isSafeInteger call.
test("Number.isSafeInteger rejects numeric-capable unions and non-unary calls", () => {
  const rejected: [string, RegExp, boolean][] = [
    ["export function f(x: number | undefined): boolean { return Number.isSafeInteger(x); }",
      /may hold a number/, true],
    ["export function f(x: number | string): boolean { return Number.isSafeInteger(x); }",
      /may hold a number/, true],
    ["export function f(): boolean { return (Number.isSafeInteger as any)(); }",
      /exactly one argument, got 0/, false],
    ["export function f(a: number, b: number): boolean { return (Number.isSafeInteger as any)(a, b); }",
      /exactly one argument, got 2/, false],
  ];
  for (const [text, message, typeChecked] of rejected) {
    for (const transform of [transformModuleDafny, transformModuleLean]) {
      let output = "";
      assert.throws(() => {
        const { typesFile, defFile } = transform(sourceModule(text, typeChecked));
        const decls = [...(typesFile?.decls ?? []), ...defFile.decls];
        output = transform === transformModuleDafny
          ? emitDafnyFile({ ...defFile, decls }, "safe.ts")
          : (resetLeanModule(), emitLeanFile({ ...defFile, decls }));
      }, message, `${text}\n${output}`);
    }
  }
});

test("Lean rejects Number.isSafeInteger on a real with the real diagnostic", () => {
  for (const arg of ["a / b", "1.5"]) {
    const text = `export function f(a: number, b: number): boolean { return Number.isSafeInteger(${arg}); }`;
    assert.throws(() => transformModuleLean(sourceModule(text)),
      /real arithmetic is not supported by the Lean backend/, arg);
  }
});
