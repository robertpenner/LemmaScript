import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { resolveOptions } from "../src/config.ts";

const source = `
export function pairwiseAtMost(a: number[], b: number[]): boolean {
  return a.length === b.length && a.every((x, i) => x <= b[i]);
}
export function hasFixedPoint(a: number[]): boolean {
  return a.some((x, i) => x === i);
}
export function plusIndex(a: number[]): number[] {
  return a.map((x, i) => x + i);
}
export function fixedPointOfDoubled(a: number[]): boolean {
  return a.concat(a).some((x, i) => x === i);
}
`;

function emit(library: "stdlib" | "local"): string {
  const project = new Project({ compilerOptions: { strict: true,
    target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [], skipLibCheck: true } });
  const file = project.createSourceFile("indexed.ts", source);
  assert.deepEqual(project.getPreEmitDiagnostics(), [], "the regression must be valid TypeScript");
  const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(file))));
  return emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] },
    "indexed.ts", resolveOptions({ "dafny-library": library }, "test"));
}

function verify(dir: string, text: string, extraArgs: string[]) {
  const proof = join(dir, "indexed.dfy");
  writeFileSync(proof, text);
  const result = spawnSync("dafny", ["verify", "--verification-time-limit", "20", ...extraArgs, proof],
    { encoding: "utf8", timeout: 120_000 });
  assert.ifError(result.error);
  return { status: result.status, output: result.stdout + result.stderr };
}

const facts = `
lemma IndexedCallbackResults()
  ensures pairwiseAtMost([1, 2], [1, 3])
  ensures plusIndex([10, 10, 10]) == [10, 11, 12]
{}

lemma EveryNeedsEachIndex()
  ensures !pairwiseAtMost([2, 0], [1, 3])
{
  assert !([2, 0][0] <= [1, 3][0]);
}

lemma SomeFindsAnIndexedWitness()
  ensures hasFixedPoint([5, 1])
  ensures fixedPointOfDoubled([9, 1])
{
  assert [5, 1][1] == 1;
  assert ([9, 1] + [9, 1])[1] == 1;
}

lemma SomeNeedsAnIndexedWitness()
  ensures !hasFixedPoint([1, 2])
{}
`;

for (const library of ["stdlib", "local"] as const) {
  test(`Dafny lowers every, some and map callbacks that read the element index (${library})`, () => {
    const output = emit(library);
    assert.doesNotMatch(output, /Unknown/, output);
    const dir = mkdtempSync(join(tmpdir(), "lsc-indexed-callbacks-"));
    try {
      const flags = library === "stdlib" ? ["--standard-libraries"] : [];
      const ok = verify(dir, output + facts, flags);
      assert.equal(ok.status, 0, ok.output);
      const wrong = verify(dir, output + facts +
        "\nlemma WrongIndex() ensures hasFixedPoint([1, 2]) {}\n", flags);
      assert.notEqual(wrong.status, 0, wrong.output);
      assert.match(wrong.output, /could not be proved|might not hold/);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
}
