import { test } from "node:test";
import assert from "node:assert/strict";
import { readdirSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { Project, ScriptTarget, SyntaxKind, type SourceFile } from "ts-morph";
import { extractModule } from "../src/extract";
import { resolveModule } from "../src/resolve";
import { narrowModule } from "../src/narrow";
import { SourceProjects } from "../src/source-projects";
import { loadConfigOptions, parseFileOptions, resolveOptions } from "../src/config";
import { checkNarrowedModule, type NarrowViolation } from "../src/narrow-checks";
import type { TExpr, TFunction, TModule, TStmt, Ty } from "../src/typedir";
import type { TypeDeclInfo } from "../src/types";

// ── Hand-built IR ───────────────────────────────────────────

const INT: Ty = { kind: "int" };
const BOOL: Ty = { kind: "bool" };
const opt = (inner: Ty): Ty => ({ kind: "optional", inner });
const BOX: Ty = { kind: "user", name: "Box" };
const v = (name: string, ty: Ty): TExpr => ({ kind: "var", name, ty });
const num = (value: number): TExpr => ({ kind: "num", value, ty: INT });
const bin = (op: string, left: TExpr, right: TExpr, ty: Ty = INT): TExpr => ({ kind: "binop", op, left, right, ty });
const fld = (obj: TExpr, field: string, ty: Ty): TExpr => ({ kind: "field", obj, field, ty });
const ret = (value: TExpr): TStmt => ({ kind: "return", value });
const match = (scrutinee: TExpr, binder: string, binderTy: Ty, someBody: TStmt[], noneBody: TStmt[] = [ret(num(0))]): TStmt =>
  ({ kind: "someMatch", scrutinee, binder, binderTy, someBody, noneBody });

const boxDecl: TypeDeclInfo = { name: "Box", kind: "record", fields: [{ name: "v", tsType: "number", type: INT, optionalKey: true }] };

function check(params: { name: string; ty: Ty }[], body: TStmt[], userNames: string[] = []): NarrowViolation[] {
  const fn: TFunction = {
    name: "f", typeParams: [], params, returnTy: INT, requires: [], ensures: [], decreases: null,
    isPure: true, forcePure: false, autohavoc: false, body,
  };
  const mod: TModule = { file: "f.ts", typeDecls: [boxDecl], externs: [], constants: [], functions: [fn], classes: [] };
  return checkNarrowedModule(mod, new Set([...userNames, ...params.map(p => p.name)]));
}

const details = (vs: NarrowViolation[]) => vs.map(x => `${x.check}: ${x.expr} -- ${x.detail}`);

test("an optional path stamped as unwrapped outside any someMatch is flagged", () => {
  const vs = check([{ name: "o", ty: opt(INT) }], [ret(bin("+", v("o", INT), num(1)))]);
  assert.deepEqual(details(vs), [
    "unwrapped-optional: o -- optional value used as an operand of +",
    "unwrapped-optional: o -- optional by declaration but typed as unwrapped, with no someMatch binding it",
  ]);
});

test("inside the Some arm the scrutinee path and the binder are unwrapped", () => {
  const vs = check([{ name: "o", ty: opt(INT) }], [
    match(v("o", opt(INT)), "_o_val", INT, [ret(bin("+", bin("+", v("o", INT), v("_o_val", INT)), num(1)))]),
  ]);
  assert.deepEqual(details(vs), []);
});

test("the None arm does not inherit the Some arm's binding", () => {
  const vs = check([{ name: "o", ty: opt(INT) }], [
    match(v("o", opt(INT)), "_o_val", INT, [ret(num(1))], [ret(bin("+", v("o", INT), num(1)))]),
  ]);
  assert.equal(vs.length, 2);
});

test("a field read through an optional receiver is flagged", () => {
  const vs = check([{ name: "b", ty: opt(BOX) }], [ret(fld(v("b", BOX), "v", opt(INT)))]);
  assert.deepEqual(details(vs), [
    "unwrapped-optional: b -- optional value used as a field receiver",
    "unwrapped-optional: b -- optional by declaration but typed as unwrapped, with no someMatch binding it",
  ]);
});

test("a field declared with ? is optional until a someMatch binds that path", () => {
  const read = fld(v("b", BOX), "v", INT);
  assert.deepEqual(details(check([{ name: "b", ty: BOX }], [ret(bin("+", read, num(1)))])), [
    "unwrapped-optional: b.v -- optional value used as an operand of +",
    "unwrapped-optional: b.v -- optional by declaration but typed as unwrapped, with no someMatch binding it",
  ]);
  const scrutinee = fld(v("b", BOX), "v", opt(INT));
  assert.deepEqual(details(check([{ name: "b", ty: BOX }], [match(scrutinee, "_b_v_val", INT, [ret(bin("+", read, num(1)))])])), []);
});

test("a field declared with ? and stamped unknown is optional until a someMatch binds that path", () => {
  // `if (a.inner === undefined || a.inner.value === undefined) return -1; return a.inner.value;`
  // before midspiral/LemmaScript#242: resolve stamps `a.inner.value` unknown and no someMatch binds it.
  const read = fld(v("b", BOX), "v", { kind: "unknown" });
  assert.deepEqual(details(check([{ name: "b", ty: BOX }], [ret(read)])), [
    "unwrapped-optional: b.v -- optional by declaration but typed as unwrapped, with no someMatch binding it",
  ]);
  const bound = check([{ name: "b", ty: BOX }], [match(fld(v("b", BOX), "v", opt(INT)), "_b_v_val", INT, [ret(read)])]);
  assert.deepEqual(details(bound), []);
});

test("an arithmetic node stamped optional inside the Some arm is flagged", () => {
  // `if (o === undefined || o + 1 > x) …` after narrow: `o` is bound, but `o + 1`
  // keeps the optional type resolve gave it, so transform matches on it again.
  const stale = bin("+", v("o", opt(INT)), num(1), opt(INT));
  const vs = check([{ name: "o", ty: opt(INT) }, { name: "x", ty: INT }], [
    match(v("o", opt(INT)), "_o_val", INT, [ret(bin(">", stale, v("x", INT), BOOL))]),
  ]);
  assert.deepEqual(details(vs), [
    "unwrapped-optional: (o + 1) -- arithmetic result typed as optional; transform will treat the value as an Option",
  ]);
});

test("a stale optional stamp on arithmetic outside a comparison is not flagged", () => {
  // `if (a.b === undefined) return -1; return a.b + 1;`: transform emits `a.b + 1`
  // unchanged and Dafny accepts it, so the stale stamp is harmless here.
  const stale = bin("+", v("o", opt(INT)), num(1), opt(INT));
  const vs = check([{ name: "o", ty: opt(INT) }], [match(v("o", opt(INT)), "_o_val", INT, [ret(stale)])]);
  assert.deepEqual(details(vs), []);
  // `o === undefined || idn(o + 1) > x`: Dafny accepts the stale sum as an int argument.
  const call: TExpr = { kind: "call", fn: v("idn", { kind: "unknown" }), args: [stale], ty: INT, callKind: "pure", paramTys: [INT] };
  const asArg = check([{ name: "o", ty: opt(INT) }], [match(v("o", opt(INT)), "_o_val", INT, [ret(call)])]);
  assert.deepEqual(details(asArg), []);
  const nested = bin("*", stale, num(2), opt(INT));
  const asOperand = check([{ name: "o", ty: opt(INT) }], [match(v("o", opt(INT)), "_o_val", INT, [ret(nested)])]);
  assert.deepEqual(details(asOperand), []);
});

test("allowed positions for an optional are not flagged", () => {
  const o = v("o", opt(INT));
  const params = [{ name: "o", ty: opt(INT) }, { name: "p", ty: opt(INT) }, { name: "x", ty: INT }];
  const allowed: TExpr[] = [
    bin("===", o, v("undefined", { kind: "unknown" }), BOOL),
    bin("!==", o, num(3), BOOL),
    bin("<", v("x", INT), o, BOOL),
    bin(">=", o, v("x", INT), BOOL),
    bin("===", o, v("p", opt(INT)), BOOL),
    { kind: "nullish", left: o, right: num(0), ty: INT },
    { kind: "unop", op: "!", expr: o, ty: BOOL },
    { kind: "call", fn: v("g", { kind: "unknown" }), args: [o], ty: INT, callKind: "pure" },
  ];
  for (const e of allowed) assert.deepEqual(details(check(params, [ret(e)])), [], JSON.stringify(e));
});

test("a relational comparison between two optionals is flagged", () => {
  const vs = check([{ name: "o", ty: opt(INT) }, { name: "p", ty: opt(INT) }],
    [ret(bin("<", v("o", opt(INT)), v("p", opt(INT)), BOOL))]);
  assert.deepEqual(details(vs), ["unwrapped-optional: (o < p) -- both operands of < are optional"]);
});

test("an optional argument for a parameter with a non-optional type is flagged", () => {
  const call = (arg: TExpr, paramTy: Ty): TExpr =>
    ({ kind: "call", fn: v("idn", { kind: "unknown" }), args: [arg], ty: INT, callKind: "pure", paramTys: [paramTy] });
  const params = [{ name: "o", ty: opt(INT) }];
  assert.deepEqual(details(check(params, [ret(call(v("o", opt(INT)), INT))])), [
    "unwrapped-optional: o -- optional value used as an argument for a parameter of type int",
  ]);
  assert.deepEqual(details(check(params, [ret(call(v("o", opt(INT)), opt(INT)))])), []);
  assert.deepEqual(details(check(params, [ret(call(v("o", opt(INT)), { kind: "user", name: "T" }))])), []);
  assert.deepEqual(details(check(params, [match(v("o", opt(INT)), "_o_val", INT, [ret(call(v("o", INT), INT))])])), []);
});

test("a binder equal to a user identifier is flagged", () => {
  const vs = check([{ name: "o", ty: opt(INT) }], [match(v("o", opt(INT)), "_o_val", INT, [ret(num(1))])], ["_o_val"]);
  assert.deepEqual(details(vs), ["binder-collision: _o_val -- binder for o equals a user identifier"]);
});

test("a nested binder reusing an outer binder's name is flagged only for a different path", () => {
  const params = [{ name: "a_b", ty: opt(INT) }, { name: "a", ty: BOX }];
  const outer = (inner: TStmt) => match(v("a_b", opt(INT)), "_a_b_val", INT, [inner]);
  const differentPath = check(params, [outer(match(fld(v("a", BOX), "v", opt(INT)), "_a_b_val", INT, [ret(num(1))]))]);
  assert.deepEqual(details(differentPath), [
    "binder-collision: _a_b_val -- binder for a.v rebinds the enclosing binder for a_b",
  ]);
  const samePath = check(params, [outer(match(v("a_b", opt(INT)), "_a_b_val", INT, [ret(num(1))]))]);
  assert.deepEqual(details(samePath), []);
});

// ── Compiled modules ────────────────────────────────────────

function narrowed(source: SourceFile, options = undefined as Parameters<typeof extractModule>[1]) {
  const userNames = new Set(source.getDescendantsOfKind(SyntaxKind.Identifier).map(i => i.getText()));
  return { mod: narrowModule(resolveModule(extractModule(source, options))), userNames };
}

const root = fileURLToPath(new URL("../..", import.meta.url));

// Fixtures that exist to show extraction rejecting a construct.
const EXPECTED_EXTRACTION_FAILURES = ["tools/fixtures/unpaired-surrogate.ts", "tools/fixtures/unsupported-extraction.ts"];

test("narrow output for every example and fixture passes both checks", () => {
  const files = ["examples", "tools/fixtures"].flatMap(dir =>
    readdirSync(path.join(root, dir)).filter(f => f.endsWith(".ts")).map(f => `${dir}/${f}`));
  const projects = new SourceProjects();
  const failures: string[] = [];
  const violations: string[] = [];
  for (const file of files) {
    const abs = path.join(root, file);
    let result;
    try {
      const source = projects.load(abs);
      const explicit = { ...loadConfigOptions(abs).explicit, ...parseFileOptions(source.getFullText(), abs) };
      result = narrowed(source, resolveOptions(explicit, abs));
    } catch {
      failures.push(file);
      continue;
    }
    for (const x of checkNarrowedModule(result.mod, result.userNames)) {
      violations.push(`${file} ${x.fn} [${x.check}] ${x.expr} -- ${x.detail}`);
    }
  }
  assert.deepEqual(failures, EXPECTED_EXTRACTION_FAILURES);
  assert.ok(files.length - failures.length >= 80, `only ${files.length - failures.length} modules checked`);
  assert.deepEqual(violations, []);
});

// Regression corpus for the optional-chain shapes fixed by
// midspiral/LemmaScript#242, including nested-path absence checks.
const chainSource = `
export interface Leaf { value?: number }
export interface Box { v?: number; inner?: Leaf }
export function andValue(x: number, o?: number): boolean { return o !== undefined && x < o; }
export function andNull(x: number, o: number | null): boolean { return o !== null && x < o; }
export function andLet(x: number, o?: number): boolean { const ok = o !== undefined && o + 1 > x; return ok; }
export function andField(b: Box): boolean { return b.v !== undefined && b.v > 0; }
export function orValue(x: number, o?: number): boolean { return o === undefined || o + 1 > x; }
export function notOrValue(x: number, o?: number): boolean { return !o || o + 1 > x; }
export function orReturn(x: number, o?: number): number { if (o === undefined || o + 1 > x) return 1; return 0; }
export function orTernary(x: number, o?: number): number { return o === undefined || o + 1 > x ? 1 : 0; }
export function andIfElse(x: number, o?: number): number { if (o !== undefined && o + 1 > x) { return 1; } else { return 0; } }
export function orCompare(x: number, o?: number): boolean { return o === undefined || x < o; }
export function guardThenCompare(x: number, o?: number): boolean { if (o === undefined) return false; return x < o; }
export function nestedOrReturn(b: Box): number { if (b.inner === undefined || b.inner.value === undefined) return -1; return b.inner.value; }
export function nestedOrCompare(x: number, b: Box): number { if (b.inner === undefined || b.inner.value === undefined || x < b.inner.value) return 1; return 0; }
`;
test("the && / || chain shapes fixed by midspiral/LemmaScript#242 pass both checks", () => {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"] }, useInMemoryFileSystem: true });
  const source = project.createSourceFile("chain.ts", chainSource);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), []);
  const { mod, userNames } = narrowed(source);
  assert.deepEqual(checkNarrowedModule(mod, userNames), []);
});
