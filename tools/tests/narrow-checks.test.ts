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

function check(params: { name: string; ty: Ty }[], body: TStmt[], userNames: string[] = [], returnTy: Ty = INT): NarrowViolation[] {
  const fn: TFunction = {
    name: "f", typeParams: [], params, returnTy, requires: [], ensures: [], decreases: null,
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
  const vs = check([{ name: "b", ty: opt(BOX) }], [ret(fld(v("b", BOX), "v", opt(INT)))], [], opt(INT));
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
    "unwrapped-optional: b.v -- optional value used as a return value of type int",
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

const ARR: Ty = { kind: "array", elem: INT };
const idx = (obj: TExpr, i: TExpr): TExpr => ({ kind: "index", obj, idx: i, ty: INT });
const letS = (name: string, ty: Ty, init: TExpr): TStmt => ({ kind: "let", name, ty, mutable: true, init });
const assign = (target: string, value: TExpr): TStmt => ({ kind: "assign", target, value });

test("an optional index operand is flagged", () => {
  const params = [{ name: "a", ty: ARR }, { name: "i", ty: opt(INT) }];
  assert.deepEqual(details(check(params, [ret(idx(v("a", ARR), v("i", opt(INT))))])), [
    "unwrapped-optional: i -- optional value used as an index operand",
  ]);
  assert.deepEqual(details(check(params, [match(v("i", opt(INT)), "_i_val", INT, [ret(idx(v("a", ARR), v("i", INT)))])])), []);
  const chain: TExpr = { kind: "optChain", obj: v("a", opt(ARR)), chain: [{ kind: "index", idx: v("i", opt(INT)), ty: opt(INT) }], ty: opt(INT) };
  assert.deepEqual(details(check([{ name: "a", ty: opt(ARR) }, { name: "i", ty: opt(INT) }], [ret(chain)], [], opt(INT))), [
    "unwrapped-optional: i -- optional value used as an index operand",
  ]);
});

test("an optional for…of iterable is flagged", () => {
  const loop = (iterable: TExpr): TStmt =>
    ({ kind: "forof", names: ["x"], nameTypes: [INT], iterable, invariants: [], doneWith: null, body: [] });
  assert.deepEqual(details(check([{ name: "xs", ty: opt(ARR) }], [loop(v("xs", opt(ARR))), ret(num(0))])), [
    "unwrapped-optional: xs -- optional value used as a for…of iterable",
  ]);
  const bound = match(v("xs", opt(ARR)), "_xs_val", ARR, [loop(v("xs", ARR)), ret(num(0))]);
  assert.deepEqual(details(check([{ name: "xs", ty: opt(ARR) }], [bound])), []);
});

test("an optional return value is flagged", () => {
  const params = [{ name: "o", ty: opt(INT) }];
  // resolve types `const y: number = o` as optional when `o` is, so the local is
  // stored safely and the fault is reported where it is returned.
  assert.deepEqual(details(check(params, [letS("y", opt(INT), v("o", opt(INT))), ret(v("y", opt(INT)))])), [
    "unwrapped-optional: y -- optional value used as a return value of type int",
  ]);
  assert.deepEqual(details(check(params, [ret(v("o", opt(INT)))])), [
    "unwrapped-optional: o -- optional value used as a return value of type int",
  ]);
  assert.deepEqual(details(check(params, [ret(v("o", opt(INT)))], [], opt(INT))), []);
  assert.deepEqual(details(check(params, [ret(v("o", opt(INT)))], [], { kind: "user", name: "T" })), []);
  // A lambda's return is judged by the lambda's own result type.
  const lambda = (result: Ty): TExpr => ({ kind: "lambda", params: [], body: [ret(v("o", opt(INT)))], ty: { kind: "fn", params: [], result } });
  assert.deepEqual(details(check(params, [{ kind: "expr", expr: lambda(INT) }, ret(num(0))])), [
    "unwrapped-optional: o -- optional value used as a return value of type int",
  ]);
  assert.deepEqual(details(check(params, [{ kind: "expr", expr: lambda(opt(INT)) }, ret(num(0))])), []);
});

test("an assignment to the scrutinee of an enclosing Some arm is flagged", () => {
  const params = [{ name: "o", ty: opt(INT) }];
  const inArm = check(params, [match(v("o", opt(INT)), "_o_val", INT, [assign("o", num(5)), ret(v("o", INT))])]);
  assert.deepEqual(details(inArm), [
    "scrutinee-assignment: o -- assignment to o inside the Some arm for o; later reads in the arm use the binder's old value",
  ]);
  const nested = check(params, [match(v("o", opt(INT)), "_o_val", INT, [{ kind: "while", cond: { kind: "bool", value: true, ty: BOOL },
    invariants: [], decreases: null, doneWith: null, body: [assign("o", num(5))] }, ret(num(0))])]);
  assert.equal(nested.length, 1);
  const receiver = check([{ name: "b", ty: BOX }], [match(fld(v("b", BOX), "v", opt(INT)), "_b_v_val", INT,
    [assign("b", { kind: "record", fields: [], ty: BOX }), ret(num(0))])]);
  assert.deepEqual(details(receiver), [
    "scrutinee-assignment: b -- assignment to b inside the Some arm for b.v; later reads in the arm use the binder's old value",
  ]);
  // Outside the Some arm, in the None arm, or after an inner let rebinds the name, nothing reads the binder.
  assert.deepEqual(details(check(params, [match(v("o", opt(INT)), "_o_val", INT, [ret(num(1))], [assign("o", num(5)), ret(num(0))])])), []);
  assert.deepEqual(details(check(params, [assign("o", num(5)), ret(num(0))])), []);
  const shadowed = check(params, [match(v("o", opt(INT)), "_o_val", INT, [letS("o", INT, num(1)), assign("o", num(2)), ret(v("o", INT))])]);
  assert.deepEqual(details(shadowed), []);
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

// Sources compiled at revision 4fa92c1 for robertpenner/LemmaScript#33. Each faulty
// function emits Dafny that `dafny resolve` rejects or that reads a stale binder;
// each clean function emits correct Dafny.
const positionPrelude = `
export interface Box { v?: number }
export interface Bag { xs?: number[] }
`;
const faultySource = positionPrelude + `
export function looseIdx(a: number[], i?: number): number { if (i != null && i >= 0 && i < a.length) return a[i]; return 0; }
export function notEqIdx(a: number[], i?: number): number { if (!(i === undefined) && i >= 0 && i < a.length) return a[i]; return 0; }
export function whileIdx(a: number[], i?: number): number { let s = 0; while (i !== undefined && i >= 0 && i < a.length) { s = a[i]; i = undefined; } return s; }
export function looseFor(xs: number[] | null): number { let s = 0; if (xs != null) { for (const x of xs) { s = s + x; } } return s; }
export function notEqLet(o?: number): number { if (!(o === undefined)) { const y: number = o; return y; } return 0; }
export function looseLetRet(o?: number): number { if (o != null) { const y = o; return y; } return 0; }
export function looseRet(o?: number): number { if (o != null) return o; return 0; }
export function assignInArm(o?: number): number { if (o !== undefined) { o = o + 1; return o; } return 0; }
export function assignField(b: Box): number { if (b.v !== undefined) { b.v = b.v + 1; return b.v; } return 0; }
export function assignEarly(o?: number): number { if (o === undefined) return 0; o = o + 1; return o; }
export function staleLocal(p?: number): number { let o = p; if (o !== undefined) { o = 5; return o; } return 0; }
export function staleLoop(p?: number): number { let o = p; let n = 0; if (o !== undefined) { while (n < 3) { o = n; n = n + 1; } return o; } return 0; }
export function receiver(b: Box): number { if (b.v !== undefined) { b = { v: 7 }; return b.v ?? 0; } return 0; }
export function assignOutside(p?: number): number { let o = p; if (o === undefined) { o = 5; } return o; }
`;
const cleanSource = positionPrelude + `
export function andIdx(a: number[], i?: number): number { if (i !== undefined && i >= 0 && i < a.length) return a[i]; return 0; }
export function earlyIdx(a: number[], i?: number): number { if (i === undefined) return 0; if (i < 0 || i >= a.length) return 0; return a[i]; }
export function ternIdx(a: number[], i?: number): number { return i !== undefined && i >= 0 && i < a.length ? a[i] : 0; }
export function fieldIdx(a: number[], b: Box): number { if (b.v !== undefined && b.v >= 0 && b.v < a.length) return a[b.v]; return 0; }
export function orIdx(a: number[], i?: number): number { if (i === undefined || i < 0 || i >= a.length) return 0; return a[i]; }
export function nullIdx(a: number[], i: number | null): number { if (i === null || i < 0 || i >= a.length) return 0; return a[i]; }
export function elseIdx(a: number[], i?: number): number { if (i === undefined) { return 0; } else { if (i >= 0 && i < a.length) return a[i]; return 0; } }
export function truthyIdx(a: number[], i?: number): number { if (i && i >= 0 && i < a.length) return a[i]; return 0; }
export function andFor(xs?: number[]): number { let s = 0; if (xs !== undefined) { for (const x of xs) { s = s + x; } } return s; }
export function earlyFor(xs?: number[]): number { if (xs === undefined) return 0; let s = 0; for (const x of xs) { s = s + x; } return s; }
export function fieldFor(b: Bag): number { let s = 0; if (b.xs !== undefined) { for (const x of b.xs) { s = s + x; } } return s; }
export function truthyFor(xs?: number[]): number { let s = 0; if (xs) { for (const x of xs) { s = s + x; } } return s; }
export function nullishFor(xs?: number[]): number { let s = 0; for (const x of xs ?? []) { s = s + x; } return s; }
export function letCopy(o?: number): number { if (o !== undefined) { const y: number = o; return y; } return 0; }
export function letEarly(o?: number): number { if (o === undefined) return 0; const y = o; return y; }
export function letField(b: Box): number { if (b.v !== undefined) { const y = b.v; return y * 2; } return 0; }
export function letTern(o?: number): number { const y = o !== undefined ? o : 0; return y + 1; }
export function letOpt(o?: number): number { const y = o; if (y !== undefined) return y + 1; return 0; }
export function letLater(o?: number): number { let y = 0; if (o !== undefined) { y = o; } return y + 1; }
export function retOpt(o?: number): number | undefined { return o; }
export function assignAfterArm(p?: number): number { let o = p; if (o !== undefined) { return o + 1; } o = 3; return 0; }
export function assignOther(p?: number): number { let o = p; let r = 0; if (o !== undefined) { r = o + 1; } return r; }
`;

function compileSource(text: string) {
  const project = new Project({ compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"] }, useInMemoryFileSystem: true });
  const source = project.createSourceFile("positions.ts", text);
  assert.deepEqual(project.getPreEmitDiagnostics().map(d => d.getMessageText()), []);
  return narrowed(source);
}

test("index, for…of, let, return and scrutinee-assignment faults from compiled sources are flagged", () => {
  const { mod, userNames } = compileSource(faultySource);
  const byFn = new Map<string, string[]>();
  for (const x of checkNarrowedModule(mod, userNames)) byFn.set(x.fn, [...byFn.get(x.fn) ?? [], `${x.check}: ${x.expr} -- ${x.detail}`]);
  const flagged = (fn: string, detail: string) =>
    assert.ok((byFn.get(fn) ?? []).some(d => d.includes(detail)), `${fn}: expected "${detail}", got ${JSON.stringify(byFn.get(fn))}`);
  for (const fn of ["looseIdx", "notEqIdx", "whileIdx"]) flagged(fn, "optional value used as an index operand");
  flagged("looseFor", "optional value used as a for…of iterable");
  for (const fn of ["notEqLet", "looseLetRet", "looseRet", "assignOutside"]) flagged(fn, "optional value used as a return value of type int");
  for (const fn of ["assignInArm", "assignField", "assignEarly", "staleLocal", "staleLoop", "receiver"]) flagged(fn, "scrutinee-assignment");
});

test("index, for…of, let, return and assignment shapes narrow supports pass the checks", () => {
  const { mod, userNames } = compileSource(cleanSource);
  assert.deepEqual(checkNarrowedModule(mod, userNames).map(x => `${x.fn} [${x.check}] ${x.expr} -- ${x.detail}`), []);
});
