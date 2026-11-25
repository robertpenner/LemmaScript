import { test } from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget } from "ts-morph";
import {
  extendFieldPlace,
  extendUnwrapPlace,
  extendVariantPlace,
  makeVarPlace,
  placeDepth,
  placeHasUnwrap,
  placeHasVariant,
  placeIsVar,
  placeRoot,
  placesMayOverlap,
} from "../src/places.ts";
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

test("places.ts pure PlacePath operations and non-overlap soundness (#49)", () => {
  const a = makeVarPlace("a");
  const b = makeVarPlace("b");
  assert.equal(placeRoot(a), "a");
  assert.equal(placeDepth(a), 0);
  assert.equal(placeIsVar(a), true);
  assert.equal(placesMayOverlap(a, b), false);

  const aItems = extendFieldPlace(extendUnwrapPlace(a), "items");
  const aCount = extendFieldPlace(extendUnwrapPlace(a), "count");
  assert.equal(placeRoot(aItems), "a");
  assert.equal(placeDepth(aItems), 2);
  assert.equal(placeHasUnwrap(aItems), true);
  assert.equal(placeHasVariant(aItems), false);
  assert.equal(placesMayOverlap(aItems, aCount), false);
  assert.equal(placesMayOverlap(aItems, aItems), true);

  const uA = extendVariantPlace(makeVarPlace("u"), "a");
  const uB = extendVariantPlace(makeVarPlace("u"), "b");
  assert.equal(placeHasVariant(uA), true);
  assert.equal(placesMayOverlap(uA, uB), false);
});

test("tools/src/places.ts self-verifies cleanly via lsc check --backend=dafny (#49)", () => {
  const res = spawnSync(
    process.execPath,
    [compiledCli, "check", "--backend=dafny", path.join(repoRoot, "tools/src/places.ts")],
    {
      cwd: repoRoot,
      encoding: "utf8",
      env: { ...process.env, LSC_RUN_LOG: "false" },
      timeout: 60_000,
    },
  );
  assert.ifError(res.error);
  const out = `${res.stdout ?? ""}\n${res.stderr ?? ""}`;
  assert.equal(res.status, 0, out);
  assert.match(out, /finished with \d+ verified, 0 errors/);
});

test("unified Place write-back verifies #350, optional arr[i]=v, nested Box.items.push, union switch push, nested field assign, and opt pop (#49)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3a-places-"));
  const programs: ImperativeProgram[] = [
    {
      family: "mutation",
      label: "issue-350-opt-array-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  if (arr !== undefined) {",
        "    arr.push(9);",
        "  }",
        "  return arr !== undefined ? arr.length : 0;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [1, 2] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "opt-array-index-assign-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  if (arr !== undefined && arr.length > 0) {",
        "    arr[0] = 10;",
        "  }",
        "  return arr !== undefined && arr.length > 0 ? arr[0] : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [1, 2] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "nested-opt-box-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.items !== undefined) {",
        "    b.items.push(7);",
        "  }",
        "  return b !== undefined && b.items !== undefined ? b.items.length : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1, 2], count: 1 } }] },
        { args: [{ kind: "opt-box", value: { items: undefined, count: 1 } }] },
      ],
    },
    {
      family: "union",
      label: "union-switch-mutate-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        'export type Item = { kind: "a"; v: number } | { kind: "b"; items: number[] };',
        "export function target(u: Item): number {",
        "  switch (u.kind) {",
        '    case "a": return u.v;',
        '    case "b": u.items.push(5); break;',
        "  }",
        '  return u.kind === "b" ? u.items.length : -1;',
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "union-ab", value: { kind: "b", items: [1, 2] } }] },
        { args: [{ kind: "union-ab", value: { kind: "a", v: 3 } }] },
      ],
    },
    {
      family: "reassign",
      label: "nested-opt-field-assign",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export interface Box { items?: number[]; count?: number }",
        "export function target(b?: Box): number {",
        "  if (b !== undefined && b.count !== undefined) {",
        "    b.count = b.count + 4;",
        "  }",
        "  return b !== undefined && b.count !== undefined ? b.count : -1;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-box", value: { items: [1], count: 3 } }] },
        { args: [{ kind: "opt-box", value: undefined }] },
      ],
    },
    {
      family: "mutation",
      label: "opt-array-pop-post-branch",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function target(arr?: number[]): number {",
        "  let popped = 0;",
        "  if (arr !== undefined && arr.length > 0) {",
        "    const last = arr.pop();",
        "    popped = last !== undefined ? last : 0;",
        "  }",
        "  return (arr !== undefined ? arr.length : 0) + popped;",
        "}",
      ].join("\n"),
      inputs: [
        { args: [{ kind: "opt-int-array", value: [3, 7] }] },
        { args: [{ kind: "opt-int-array", value: undefined }] },
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
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});

test("non-Place mutating collection call fails closed with clear diagnostic (#49)", () => {
  const project = makeProject();
  const workDir = mkdtempSync(path.join(tmpdir(), "lsc-m3a-nonplace-"));
  try {
    const nonPlace: ImperativeProgram = {
      family: "mutation",
      label: "non-place-push",
      fnName: "target",
      returnKind: "number",
      tsText: [
        "export function getArr(): number[] { return [1, 2]; }",
        "export function target(): number {",
        "  getArr().push(3);",
        "  return 0;",
        "}",
      ].join("\n"),
      inputs: [{ args: [] }],
    };
    const out = evaluateImperativeProgram(nonPlace, {
      project,
      workDir,
      counts: createImperativeCounts(),
      timeoutSec: 15,
    });
    assert.equal(out.ok, false);
    assert.equal(out.oracle, "rejected");
    assert.match(out.detail, /not a writable Place rooted at a variable/);
  } finally {
    rmSync(workDir, { recursive: true, force: true });
  }
});
