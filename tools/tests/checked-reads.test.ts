import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import { extractModule } from "../src/extract.ts";
import { resolveModule } from "../src/resolve.ts";
import { narrowModule } from "../src/narrow.ts";
import { transformModuleDafny, transformModuleLean } from "../src/transform.ts";
import { emitDafnyFile } from "../src/dafny-emit.ts";
import { emitLeanFile } from "../src/lean-emit.ts";
import {
  createImperativeCounts,
  evaluateImperativeProgram,
  type ImperativeProgram,
} from "../fuzz/imperative-oracle.ts";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const compiledCli = path.join(repoRoot, "tools/dist/lsc.js");

function makeProject() {
  return new Project({
    compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
    useInMemoryFileSystem: true,
  });
}

test("Milestone 4 (#52): #349 precondition preservation across ===, !==, and relational comparisons without pi comparison-temp churn", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-349-"));
  const guardDef = [
    "//@ requires ok",
    "export function guard(ok: boolean, v: number): number { return v; }",
  ].join("\n");

  const programs: ImperativeProgram[] = [
    {
      family: "guard-eval",
      label: "eq-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x === guard(false, 1); }`,
      inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
    },
    {
      family: "guard-eval",
      label: "neq-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== guard(false, 1); }`,
      inputs: [{ args: [{ kind: "opt-int", value: undefined }] }],
    },
    {
      family: "guard-eval",
      label: "lt-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== undefined && x < guard(false, 1); }`,
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 0 }] },
      ],
    },
    {
      family: "guard-eval",
      label: "le-rhs-guard-false",
      fnName: "target",
      returnKind: "boolean",
      tsText: `${guardDef}\nexport function target(x?: number): boolean { return x !== undefined && x <= guard(false, 1); }`,
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 1 }] },
      ],
    },
  ];

  try {
    for (const prog of programs) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }

    // Pure comparison (`x === "bytes"`) emits zero `i_compare` temporary churn.
    const sf = project.createSourceFile(
      "pi_pure_cmp.ts",
      `export function isBytes(truncatedBy?: string): boolean { return truncatedBy === "bytes"; }`,
      { overwrite: true },
    );
    const { typesFile, defFile } = transformModuleDafny(narrowModule(resolveModule(extractModule(sf))));
    const dfy = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "pi_pure_cmp.ts");
    assert.ok(!dfy.includes("i_compare"), `unexpected comparison temp churn:\n${dfy}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 4 (#52): #340 definite assignment narrowing, #339 while presence narrowing, and #268 &&/|| chains verify in Dafny and emit clean Lean", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-reads-"));
  const programs: ImperativeProgram[] = [
    {
      family: "reassign",
      label: "issue-340-if-undefined-assign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(x?: number): number {",
        "  let v: number | undefined = x;",
        "  if (v === undefined) {",
        "    v = 6;",
        "  }",
        "  return v + 3;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 4 }] },
      ],
    },
    {
      family: "reassign",
      label: "issue-340-direct-assign-clear-reassign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(x?: number): number {",
        "  let v: number | undefined = x;",
        "  v = 6;",
        "  const first = v + 1;",
        "  v = undefined;",
        "  return v !== undefined ? v : first;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int", value: undefined }] },
        { args: [{ kind: "opt-int", value: 9 }] },
      ],
    },
    {
      family: "reassign",
      label: "issue-268-return-and-and-or-chains",
      fnName: "target",
      returnKind: "boolean",
      tsText: [
        "export function target(x: number, o?: number): boolean {",
        "  return o !== undefined && x < o;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "int", value: 3 }, { kind: "opt-int", value: undefined }] },
        { args: [{ kind: "int", value: 3 }, { kind: "opt-int", value: 5 }] },
        { args: [{ kind: "int", value: 7 }, { kind: "opt-int", value: 5 }] },
      ],
    },
  ];

  try {
    for (const prog of programs) {
      const out = evaluateImperativeProgram(prog, {
        project,
        workDir,
        counts: createImperativeCounts(),
        timeoutSec: 15,
        stages: ["pre", "opt"],
      });
      assert.equal(out.ok, true, `${prog.label} failed (${out.oracle}): ${out.detail}`);
    }

    // #339 while presence narrowing with contract verified end-to-end via `lsc check --backend=dafny`.
    const whileSrc = [
      "export function target(start?: number): number {",
      "  //@ ensures \\result >= 0",
      "  let cur: number | undefined = start;",
      "  let steps = 0;",
      "  let total = 0;",
      "  while (cur !== undefined && cur >= 0 && steps < 3) {",
      "    //@ invariant steps >= 0 && total >= 0",
      "    //@ decreases 3 - steps",
      "    total = total + cur;",
      "    steps = steps + 1;",
      "    cur = cur > 0 ? cur - 1 : undefined;",
      "  }",
      "  return total;",
      "}",
    ].join("\n");
    const whileFile = path.join(workDir, "while_presence.ts");
    writeFileSync(whileFile, whileSrc);
    const whileRes = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", whileFile], {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    });
    assert.equal(whileRes.status, 0, `${whileRes.stdout}\n${whileRes.stderr}`);

    // Lean emission uses `.get (by grind)` for pure `checkedUnwrap` without removing Pure companions.
    const sf = project.createSourceFile(
      "lean_checked.ts",
      `export function cmpAnd(x: number, o?: number): boolean { return o !== undefined && x < o; }`,
      { overwrite: true },
    );
    const leanMod = transformModuleLean(narrowModule(resolveModule(extractModule(sf))));
    const leanTypes = leanMod.typesFile ? emitLeanFile(leanMod.typesFile) : "";
    const leanDef = emitLeanFile(leanMod.defFile);
    assert.match(leanTypes, /\.get \(by grind\)/, `expected Lean checked Option.get in typesFile:\n${leanTypes}`);
    assert.match(leanDef, /Pure\.cmpAnd/, `expected Pure companion preserved in Lean defFile:\n${leanDef}`);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("Milestone 4 (#52): upstream reproductions #342, #352, #353, #354 verify cleanly via lsc check --backend=dafny", () => {
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m4-upstream-"));
  const cases: Array<{ name: string; code: string }> = [
    {
      name: "issue_342.ts",
      code: [
        "interface C { v: number }",
        "export function f1(a?: number): number {",
        "  //@ ensures \\result === 10",
        "  if (a !== undefined) { a = 10; return a; }",
        "  return 10;",
        "}",
        "export function f2(c?: C): number {",
        "  //@ ensures c !== undefined ==> \\result === 1",
        "  if (c !== undefined) { c.v = 1; }",
        "  return c !== undefined ? c.v : 0;",
        "}",
        "export function f3(a?: number): number {",
        "  //@ ensures \\result === 0",
        "  if (a !== undefined) { a = undefined; return a !== undefined ? a : 0; }",
        "  return 0;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_352.ts",
      code: [
        "export function nullishPlain(x: number): number {",
        "  //@ ensures \\result === x",
        "  return x ?? 0;",
        "}",
        "export function nullishNarrowed(o?: number): number {",
        "  //@ ensures o !== undefined ==> \\result === o",
        "  if (o !== undefined) { return o ?? 0; }",
        "  return -1;",
        "}",
        "export function optChainPlain(s: string): number {",
        "  //@ ensures \\result === s.length",
        "  return s?.length;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_353.ts",
      code: [
        "export function f1(xs: number[], o?: number): number[] {",
        "  if (o !== undefined) { return xs.map(x => x + o); }",
        "  return xs;",
        "}",
        "export function f2(n?: number): number {",
        "  if (n !== undefined && n >= 0) {",
        "    let i = 0;",
        "    while (i < n) {",
        "      //@ invariant 0 <= i && i <= n",
        "      //@ decreases n - i",
        "      i = i + 1;",
        "    }",
        "    return i;",
        "  }",
        "  return 0;",
        "}",
      ].join("\n"),
    },
    {
      name: "issue_354.ts",
      code: [
        "export interface Box { tag: number; inner?: number }",
        "export interface Deep { b?: Box }",
        "export function f1(b?: Box): number {",
        "  //@ ensures b !== undefined && b.tag === 1 && b.inner !== undefined ==> \\result === b.inner",
        "  if (b?.tag !== 1) return 0;",
        "  if (b.inner !== undefined) return b.inner;",
        "  return 0;",
        "}",
        "export function f2(d: Deep): number {",
        "  //@ ensures d.b !== undefined && d.b.inner !== undefined ==> \\result === d.b.inner",
        "  if (d.b === undefined) return 0;",
        "  if (d.b.inner !== undefined) return d.b.inner;",
        "  return 0;",
        "}",
      ].join("\n"),
    },
  ];
  try {
    for (const c of cases) {
      const f = path.join(workDir, c.name);
      writeFileSync(f, c.code);
      const res = spawnSync(process.execPath, [compiledCli, "check", "--backend=dafny", f], {
        cwd: repoRoot,
        encoding: "utf8",
        env: { ...process.env, LSC_RUN_LOG: "false" },
        timeout: 60_000,
      });
      assert.equal(res.status, 0, `${c.name} failed:\n${res.stdout}\n${res.stderr}`);
    }
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
