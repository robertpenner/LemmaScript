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
import { transformModuleDafny } from "../src/transform";
import { emitDafnyFile } from "../src/dafny-emit";
import type { TStmt } from "../src/typedir";

// Two for-of loops over the same head name in one function. The second loop's
// counter is `_x_idx2`, and its invariant names it, so resolve must bind the
// same counter name that transform emits for each loop.
const source = `
export function countTwice(xs: number[]): number {
  //@ ensures \\result === 2 * xs.length
  let n = 0;
  for (const x of xs) {
    //@ invariant n === _x_idx
    n = n + 1;
  }
  let m = 0;
  for (const x of xs) {
    //@ invariant n === xs.length && m === _x_idx2
    m = m + 1;
  }
  return n + m;
}
`;

function sourceModule() {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("count.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  return narrowModule(resolveModule(extractModule(file)));
}

function emitDafny() {
  const { typesFile, defFile } = transformModuleDafny(sourceModule());
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "count.ts");
}

function verify(text: string) {
  const dir = mkdtempSync(join(tmpdir(), "lsc-loop-counters-"));
  try {
    const proof = join(dir, "count.dfy");
    writeFileSync(proof, text);
    const result = spawnSync("dafny", ["verify", "--verification-time-limit", "30", proof], { encoding: "utf8", timeout: 180_000 });
    assert.ifError(result.error);
    return { status: result.status, output: result.stdout + result.stderr };
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

test("resolve records the counter name transform emits for each for-of loop", () => {
  const fn = sourceModule().functions.find(f => f.name === "countTwice")!;
  const loops = fn.body.filter((s): s is TStmt & { kind: "forof" } => s.kind === "forof");
  assert.deepEqual(loops.map(l => l.idx), ["_x_idx", "_x_idx2"]);
  // Resolve splits the conjunction; the second invariant is `m === _x_idx2`.
  const counterRef = loops[1].invariants[1];
  assert.equal(counterRef.kind, "binop");
  if (counterRef.kind !== "binop") return;
  assert.deepEqual(counterRef.right, { kind: "var", name: "_x_idx2", ty: { kind: "nat" } });
});

test("a spec naming the second loop's counter verifies", () => {
  const output = emitDafny();
  assert.match(output, /var i_x_idx := 0;/);
  assert.match(output, /var i_x_idx2 := 0;/);
  assert.match(output, /invariant \(m == i_x_idx2\)/);
  const result = verify(output);
  assert.equal(result.status, 0, result.output);
});
