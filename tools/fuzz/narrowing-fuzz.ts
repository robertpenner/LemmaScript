/**
 * Narrowing fuzzer: generates small TypeScript modules that guard optional
 * values and then use them, compiles each module in-process, and reports
 * modules the compiler mishandles.
 *
 * Each module goes through extract → resolve → narrow. The narrowed IR is
 * checked by `checkNarrowedModule` (see src/narrow-checks.ts). Modules that
 * pass those checks are lowered to Dafny and run through `dafny resolve`.
 * A compiler exception is reported as a rejection, and a module with
 * TypeScript errors as a generator bug (`invalid-ts`).
 *
 * Failures are grouped by oracle and a normalized message. Each round runs
 * fast-check with a property that only fails for a class not seen in an
 * earlier round, so every round can find and shrink a different class.
 *
 * Usage (from tools/):
 *   npm run fuzz:narrowing -- [--seed N] [--runs N] [--classes N] [--minutes N] [--out DIR] [--positions P,Q]
 *   npm run fuzz:narrowing -- --seed N --path P   replay one round's counterexample
 *   npm run fuzz:narrowing -- --file DIR/1.ts     run the oracles on a saved module
 *
 * Defaults: seed 1, 150 runs per round, stop after 12 classes or 9 minutes.
 * `--positions` limits the statement forms generated (names in POSITIONS),
 * for example to search past a known bug in `&&`/`||` chains used as values.
 * A replay with `--path` needs the same `--positions` as the original run.
 * Needs `dafny` on PATH. Exits 1 when it reports a failure.
 */

import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { parseArgs } from "node:util";
import fc from "fast-check";
import { Project, ScriptTarget, SyntaxKind } from "ts-morph";
import { extractModule } from "../src/extract.js";
import { resolveModule } from "../src/resolve.js";
import { narrowModule } from "../src/narrow.js";
import { checkNarrowedModule } from "../src/narrow-checks.js";
import { transformModuleDafny } from "../src/transform.js";
import { emitDafnyFile } from "../src/dafny-emit.js";
import type { TModule } from "../src/typedir.js";

// ── Generated programs ──────────────────────────────────────

/** An optional number reachable from the parameters, and the optional paths that must be guarded before it. */
interface Target { path: string; prereqs: string[]; nullable: boolean }

const TARGETS: Target[] = [
  { path: "o", prereqs: [], nullable: false },
  { path: "p", prereqs: [], nullable: false },
  { path: "n", prereqs: [], nullable: true },
  { path: "a_b", prereqs: [], nullable: false },
  { path: "a.b", prereqs: [], nullable: false },
  { path: "a.v", prereqs: [], nullable: false },
  { path: "a.inner.value", prereqs: ["a.inner"], nullable: false },
  { path: "box.b", prereqs: ["box"], nullable: false },
  { path: "box.inner.value", prereqs: ["box", "box.inner"], nullable: false },
];

// Required parameters first: TypeScript rejects a required parameter after an optional one.
const PARAMS: Record<string, string> = {
  n: "n: number | null", a: "a: Box", o: "o?: number", p: "p?: number", a_b: "a_b?: number", box: "box?: Box",
};

const POSITIONS = [
  "returnAnd", "constAnd", "callArg", "returnOr", "ifThen", "ifElse", "ternaryBool",
  "ternaryValue", "ifValue", "earlyReturnOr", "guardThenUse", "nestedIf", "constTernary",
] as const;
type Position = typeof POSITIONS[number];
const BOOL_POSITIONS: ReadonlySet<Position> = new Set(["returnAnd", "constAnd", "callArg", "returnOr"]);

interface FnSpec {
  targets: number[];   // indices into TARGETS
  truthy: boolean[];   // per guard, in order: a truthiness test instead of a comparison
  position: Position;
  use: number;
  ensures: boolean;
}

function moduleArb(positions: readonly Position[]): fc.Arbitrary<FnSpec[]> {
  const fnArb: fc.Arbitrary<FnSpec> = fc.record({
    targets: fc.uniqueArray(fc.nat(TARGETS.length - 1), { minLength: 1, maxLength: 2 }),
    truthy: fc.array(fc.boolean(), { minLength: 6, maxLength: 6 }),
    position: fc.constantFrom(...positions),
    use: fc.nat(4),
    ensures: fc.boolean(),
  });
  return fc.array(fnArb, { minLength: 1, maxLength: 3 });
}

const indent = (s: string) => s.split("\n").map(l => "  " + l).join("\n");

function renderFn(spec: FnSpec, name: string): string {
  const targets = spec.targets.map(i => TARGETS[i]);
  const guards: { path: string; missing: string }[] = [];
  for (const t of targets) {
    for (const pre of t.prereqs) if (!guards.some(g => g.path === pre)) guards.push({ path: pre, missing: "undefined" });
    guards.push({ path: t.path, missing: t.nullable ? "null" : "undefined" });
  }
  const present = guards.map((g, i) => spec.truthy[i] ? g.path : `${g.path} !== ${g.missing}`);
  const absent = guards.map((g, i) => spec.truthy[i] ? `!${g.path}` : `${g.path} === ${g.missing}`);
  const has = present.join(" && ");
  // A chain used as a boolean value needs boolean operands: `o && x < o` has type number | boolean | undefined.
  const hasBool = guards.map((g, i) => spec.truthy[i] ? `!!${g.path}` : present[i]).join(" && ");
  const lacks = absent.join(" || ");

  const term = targets.map(t => t.path).join(" + ");
  const cond = [`x < ${term}`, `${term} + 1 > x`, `${term} > 0`, `${term} - x > 0`, `idn(${term}) > x`][spec.use];
  const value = [term, `${term} + 1`, `${term} - x`, `idn(${term})`, `${term} * 2`][spec.use];

  let nested = `return ${value};`;
  for (const g of [...present].reverse()) nested = `if (${g}) {\n${indent(nested)}\n}`;

  const body: Record<Position, string> = {
    returnAnd: `return ${hasBool} && ${cond};`,
    constAnd: `const ok = ${hasBool} && ${cond};\nreturn ok;`,
    callArg: `return check(${hasBool} && ${cond});`,
    returnOr: `return ${lacks} || ${cond};`,
    ifThen: `if (${has} && ${cond}) {\n  return 1;\n}\nreturn 0;`,
    ifElse: `if (${has} && ${cond}) {\n  return 1;\n} else {\n  return 0;\n}`,
    ternaryBool: `return ${has} && ${cond} ? 1 : 0;`,
    ternaryValue: `return ${has} ? ${value} : -1;`,
    ifValue: `if (${has}) {\n  return ${value};\n}\nreturn -1;`,
    earlyReturnOr: `if (${lacks} || ${cond}) return 1;\nreturn 0;`,
    guardThenUse: `if (${lacks}) return -1;\nreturn ${value};`,
    nestedIf: `${nested}\nreturn -1;`,
    constTernary: `const y = ${has} ? ${value} : -1;\nreturn y;`,
  };

  const roots = new Set(guards.map(g => g.path.split(".")[0]));
  const params = ["x: number", ...Object.keys(PARAMS).filter(r => roots.has(r)).map(r => PARAMS[r])];
  const returns = BOOL_POSITIONS.has(spec.position) ? "boolean" : "number";
  const ensures = spec.ensures ? `//@ ensures ${has} ==> ${cond}\n` : "";
  return `export function ${name}(${params.join(", ")}): ${returns} {\n${indent(ensures + body[spec.position])}\n}`;
}

const PRELUDE = `export interface Leaf { value?: number }
export interface Box { inner?: Leaf; b?: number; v?: number }
export function idn(k: number): number { return k; }
export function check(flag: boolean): boolean { return flag; }
`;

function renderModule(fns: FnSpec[]): string {
  return PRELUDE + "\n" + fns.map((f, i) => renderFn(f, `f${i}`)).join("\n\n") + "\n";
}

// ── Oracles ─────────────────────────────────────────────────

type Failure = { oracle: "invalid-ts" | "rejected" | "checks" | "dafny"; signature: string; detail: string; dfy?: string };
type Outcome = { ok: true } | ({ ok: false } & Failure);

const project = new Project({
  compilerOptions: { strict: true, target: ScriptTarget.ESNext, lib: ["lib.esnext.d.ts"], types: [] },
  useInMemoryFileSystem: true,
});
const workDir = mkdtempSync(path.join(tmpdir(), "lsc-narrowing-fuzz-"));
const cache = new Map<string, Outcome>();
const counts = { modules: 0, dafnyCalls: 0 };

/** Removes generated names, binders and line/column numbers so one bug gives one signature. */
function normalize(message: string): string {
  return message
    .replace(/\b_[A-Za-z0-9_]*\b/g, "_")
    .replace(/\b(f\d+|o|p|n|a_b|a|box|x)\b/g, "v")
    .replace(/\d+/g, "N")
    .trim();
}

function dafnyResolve(dfy: string): string | null {
  const file = path.join(workDir, "gen.dfy");
  writeFileSync(file, dfy);
  counts.dafnyCalls++;
  const result = spawnSync("dafny", ["resolve", file], { encoding: "utf8", timeout: 120_000 });
  if (result.error) throw result.error;
  if (result.status === 0) return null;
  const output = (result.stdout + result.stderr).replaceAll(workDir + path.sep, "");
  const errors = output.split("\n").filter(l => / Error: /.test(l));
  return errors.length > 0 ? errors.join("\n") : output.trim();
}

function evaluate(text: string): Outcome {
  const source = project.createSourceFile("gen.ts", text, { overwrite: true });
  const diagnostics = project.getPreEmitDiagnostics().map(d => {
    const m = d.getMessageText();
    return typeof m === "string" ? m : m.getMessageText();
  });
  if (diagnostics.length > 0) {
    return { ok: false, oracle: "invalid-ts", signature: `invalid-ts: ${normalize(diagnostics[0])}`, detail: diagnostics.join("\n") };
  }
  let narrowed: TModule;
  let dfy: string;
  try {
    narrowed = narrowModule(resolveModule(extractModule(source)));
    const { typesFile, defFile } = transformModuleDafny(narrowed);
    dfy = emitDafnyFile({ ...defFile, decls: [...(typesFile?.decls ?? []), ...defFile.decls] }, "gen.ts");
  } catch (e) {
    const message = e instanceof Error ? e.message : String(e);
    return { ok: false, oracle: "rejected", signature: `rejected: ${normalize(message.split("\n")[0])}`, detail: message };
  }
  const userNames = new Set(source.getDescendantsOfKind(SyntaxKind.Identifier).map(i => i.getText()));
  const violations = checkNarrowedModule(narrowed, userNames);
  if (violations.length > 0) {
    return { ok: false, oracle: "checks", signature: `checks: ${violations[0].check}: ${violations[0].detail}`,
      detail: violations.map(v => `${v.fn} [${v.check}] ${v.expr} -- ${v.detail}`).join("\n"), dfy };
  }
  const errors = dafnyResolve(dfy);
  if (errors === null) return { ok: true };
  return { ok: false, oracle: "dafny", signature: `dafny: ${normalize(errors.split("\n")[0].replace(/^.*? Error: /, ""))}`,
    detail: errors, dfy };
}

function run(text: string): Outcome {
  let outcome = cache.get(text);
  if (!outcome) {
    counts.modules++;
    outcome = evaluate(text);
    cache.set(text, outcome);
  }
  return outcome;
}

/** Full report for one module. A module flagged by the checks is also given to Dafny, to show whether Dafny agrees. */
function describe(outcome: Outcome): string {
  if (outcome.ok) return "ok: the checks pass and dafny resolve accepts the module";
  let report = `${outcome.signature}\n${outcome.detail}`;
  if (outcome.oracle === "checks" && outcome.dfy !== undefined) {
    const errors = dafnyResolve(outcome.dfy);
    report += `\ndafny resolve: ${errors === null ? "accepts the module" : "rejects the module\n" + errors}`;
  }
  return report;
}

// ── Driver ──────────────────────────────────────────────────

const { values: args } = parseArgs({
  options: {
    seed: { type: "string", default: "1" },
    runs: { type: "string", default: "150" },
    classes: { type: "string", default: "12" },
    positions: { type: "string", default: POSITIONS.join(",") },
    minutes: { type: "string", default: "9" },
    out: { type: "string" },
    path: { type: "string" },
    file: { type: "string" },
    help: { type: "boolean", default: false },
  },
});

function main(): number {
  if (args.help) {
    console.log(readFileSync(new URL(import.meta.url), "utf8").split("*/")[0].replace(/^\/\*\*\n/, "").replace(/^ \* ?/gm, ""));
    return 0;
  }
  if (args.file) {
    const outcome = run(readFileSync(args.file, "utf8"));
    console.log(describe(outcome));
    return outcome.ok ? 0 : 1;
  }

  const seed = Number(args.seed);
  const numRuns = Number(args.runs);
  const positions = args.positions.split(",").map(p => p.trim()) as Position[];
  const unknown = positions.filter(p => !POSITIONS.includes(p));
  if (unknown.length > 0) {
    console.error(`unknown positions: ${unknown.join(", ")}; choose from ${POSITIONS.join(", ")}`);
    return 2;
  }
  const arb = moduleArb(positions);
  if (args.path) {
    const result = fc.check(fc.property(arb, fns => run(renderModule(fns)).ok), { seed, path: args.path, numRuns });
    if (!result.failed || !result.counterexample) {
      console.log("replay passed");
      return 0;
    }
    const text = renderModule(result.counterexample[0]);
    console.log(`${text}\n${describe(run(text))}`);
    return 1;
  }

  const out = args.out ?? path.join(tmpdir(), `lsc-narrowing-fuzz-seed${seed}`);
  mkdirSync(out, { recursive: true });
  const started = Date.now();
  const deadline = started + Number(args.minutes) * 60_000;
  const seen = new Set<string>();
  let stop = "class limit reached";

  for (let round = 0; seen.size < Number(args.classes); round++) {
    const remaining = deadline - Date.now();
    if (remaining <= 0) { stop = "time limit reached"; break; }
    const roundSeed = seed + round;
    const result = fc.check(fc.property(arb, fns => {
      const outcome = run(renderModule(fns));
      return outcome.ok || seen.has(outcome.signature);
    }), { seed: roundSeed, numRuns, interruptAfterTimeLimit: remaining, markInterruptAsFailure: false });
    if (!result.failed || !result.counterexample) {
      stop = result.interrupted ? "time limit reached" : `round with seed ${roundSeed} found no new class in ${numRuns} runs`;
      break;
    }
    const text = renderModule(result.counterexample[0]);
    const outcome = run(text);
    if (outcome.ok) continue;
    seen.add(outcome.signature);
    const n = seen.size;
    writeFileSync(path.join(out, `${n}.ts`), text);
    if (outcome.dfy !== undefined) writeFileSync(path.join(out, `${n}.dfy`), outcome.dfy);
    console.log(`── class ${n}: replay with --seed ${roundSeed} --path ${result.counterexamplePath} ──\n${text}\n${describe(outcome)}\n`);
  }

  const seconds = ((Date.now() - started) / 1000).toFixed(1);
  console.log(`${seen.size} failure classes; stopped: ${stop}`);
  console.log(`${counts.modules} distinct modules compiled, ${counts.dafnyCalls} dafny calls, ${seconds}s`);
  console.log(`counterexamples saved to ${out}`);
  return seen.size === 0 ? 0 : 1;
}

try {
  process.exitCode = main();
} finally {
  rmSync(workDir, { recursive: true, force: true });
}
