#!/usr/bin/env node
// Generates JavaScript Math.* special-value vectors from the running engine.
// The output records what this engine returned. It is not an oracle for the
// approximated members: their finite results are implementation-approximated
// in ECMAScript and may differ in the last bits across engines and versions.
//
// Usage (from the repository root):
//   node spikes/math-semantics/vectors/gen.mjs           write math-special-values.json
//   node spikes/math-semantics/vectors/gen.mjs --check   regenerate and compare, exit 1 on mismatch
//
// Deterministic: fixed input list, no randomness, no network. Math.random is excluded.

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
const outFile = join(here, 'math-special-values.json');

const SPEC_EDITION =
  'ECMAScript 2026 Language Specification (https://tc39.es/ecma262/2026/multipage/, fetched 2026-11-19)';

function hex(x) {
  const dv = new DataView(new ArrayBuffer(8));
  dv.setFloat64(0, x, false);
  let s = '0x';
  for (let i = 0; i < 8; i++) s += dv.getUint8(i).toString(16).padStart(2, '0');
  return s;
}

function literal(x) {
  if (Number.isNaN(x)) return 'NaN';
  if (x === Infinity) return 'Infinity';
  if (x === -Infinity) return '-Infinity';
  if (Object.is(x, -0)) return '-0';
  return String(x);
}

function value(x) {
  return { js: literal(x), hex: hex(x) };
}

const isZero = (x) => x === 0;
const isNaNOrInfOrZero = (x) => Number.isNaN(x) || !Number.isFinite(x) || x === 0;

// Unary inputs: signed zeros, NaN, infinities, small integers, halves (round ties),
// subnormal and extreme magnitudes, and the 2^53 neighbourhood.
const UNARY = [
  0, -0, NaN, Infinity, -Infinity,
  1, -1, 2, -8, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, 0.49999999999999994, -0.49999999999999994,
  Number.MIN_VALUE, -Number.MIN_VALUE, Number.MAX_VALUE, -Number.MAX_VALUE,
  2 ** 53 - 1, 2 ** 53, 2 ** 53 + 2, 2 ** 31, -(2 ** 31), 2 ** 32, 4294967295,
  Math.PI, Math.PI / 2, 1e-300, 3.4028235677973366e38,
];

// Binary inputs: a cross product of a small special set, subnormal and extreme
// pairs shared by every binary member, plus targeted pairs per member.
const BINARY_BASE = [0, -0, NaN, Infinity, -Infinity, 1, -1, 0.5, -0.5, 2, -2];
const BINARY_COMMON = [
  [Number.MIN_VALUE, 2], [-Number.MIN_VALUE, 2], [2, Number.MIN_VALUE], [2, -Number.MIN_VALUE],
  [Number.MIN_VALUE, Number.MIN_VALUE], [-Number.MIN_VALUE, -Number.MIN_VALUE],
  [Number.MAX_VALUE, Number.MAX_VALUE], [-Number.MAX_VALUE, Number.MAX_VALUE],
  [Number.MAX_VALUE, 2], [2, Number.MAX_VALUE],
];
// Argument lists for the variadic members (Math.min, Math.max, Math.hypot) at
// arities other than 2: no arguments, one argument, and three arguments.
const VARIADIC = [
  [], [NaN], [-0], [0], [Infinity], [-Infinity], [-5],
  [1, -0, 0], [-0, 0, -0], [1, NaN, Infinity], [Infinity, NaN, 1], [-Infinity, 1, 2], [3, 4, 12],
];
const BINARY_EXTRA = {
  pow: [
    [-8, 1 / 3], [-1, 0.5], [0, -1], [-0, -1], [-0, -3], [-0, 3], [2, 1024], [2, -1075],
    [0.5, Infinity], [0.5, -Infinity], [1.5, Infinity], [1.5, -Infinity], [-2, 3], [-2, 0.5],
  ],
  atan2: [[1, 1], [-1, -1], [1, -1], [-1, 1]],
  hypot: [[3, 4], [Number.MAX_VALUE, Number.MAX_VALUE], [Infinity, NaN], [NaN, -Infinity]],
  imul: [[2 ** 31, 2], [4294967295, 5], [0xffffffff, 0xffffffff], [1.9, 3.9], [-1.9, 3.9]],
  min: [[1, 2], [-0, 0]],
  max: [[1, 2], [-0, 0]],
};

// Classification follows the specification step that produced the result.
// `exact`: the step fixes a single Number value (a listed special case, or an
// exactly specified operation such as 𝔽(the square root of ℝ(n))).
// `approximated`: the step returns an implementation-approximated Number value,
// including special cases the spec states with an approximation (for example
// atan(+∞) is "an implementation-approximated Number value representing π / 2").
const exact = () => 'exact';

function finiteApprox(specialIf) {
  return (...args) => (specialIf(...args) ? 'exact' : 'approximated');
}

const MEMBERS = {
  abs: { arity: 1, fn: Math.abs, classify: exact },
  min: { arity: 'variadic', fn: Math.min, classify: exact },
  max: { arity: 'variadic', fn: Math.max, classify: exact },
  floor: { arity: 1, fn: Math.floor, classify: exact },
  ceil: { arity: 1, fn: Math.ceil, classify: exact },
  round: { arity: 1, fn: Math.round, classify: exact },
  trunc: { arity: 1, fn: Math.trunc, classify: exact },
  sign: { arity: 1, fn: Math.sign, classify: exact },
  sqrt: { arity: 1, fn: Math.sqrt, classify: exact },
  imul: { arity: 2, fn: Math.imul, classify: exact },
  fround: { arity: 1, fn: Math.fround, classify: exact },
  clz32: { arity: 1, fn: Math.clz32, classify: exact },
  // cbrt: NaN, ±0, ±∞ are returned unchanged.
  cbrt: { arity: 1, fn: Math.cbrt, classify: finiteApprox(isNaNOrInfOrZero) },
  // exp: NaN or +∞ -> n; ±0 -> 1; -∞ -> +0.
  exp: { arity: 1, fn: Math.exp, classify: finiteApprox((x) => Number.isNaN(x) || !Number.isFinite(x) || x === 0) },
  // expm1: NaN, ±0, +∞ -> n; -∞ -> -1.
  expm1: { arity: 1, fn: Math.expm1, classify: finiteApprox(isNaNOrInfOrZero) },
  // log: NaN or +∞ -> n; 1 -> +0; ±0 -> -∞; < 0 -> NaN.
  log: { arity: 1, fn: Math.log, classify: finiteApprox((x) => Number.isNaN(x) || x === Infinity || x === 1 || x === 0 || x < 0) },
  // log1p: NaN, ±0, +∞ -> n; -1 -> -∞; < -1 -> NaN.
  log1p: { arity: 1, fn: Math.log1p, classify: finiteApprox((x) => Number.isNaN(x) || x === 0 || x === Infinity || x <= -1) },
  log2: { arity: 1, fn: Math.log2, classify: finiteApprox((x) => Number.isNaN(x) || x === Infinity || x === 1 || x === 0 || x < 0) },
  log10: { arity: 1, fn: Math.log10, classify: finiteApprox((x) => Number.isNaN(x) || x === Infinity || x === 1 || x === 0 || x < 0) },
  // sin, tan: NaN, ±0 -> n; ±∞ -> NaN.  cos: NaN -> NaN; ±∞ -> NaN; ±0 -> 1.
  sin: { arity: 1, fn: Math.sin, classify: finiteApprox(isNaNOrInfOrZero) },
  cos: { arity: 1, fn: Math.cos, classify: finiteApprox(isNaNOrInfOrZero) },
  tan: { arity: 1, fn: Math.tan, classify: finiteApprox(isNaNOrInfOrZero) },
  // atan: NaN, ±0 -> n; ±∞ -> approximated ±π/2.
  atan: { arity: 1, fn: Math.atan, classify: finiteApprox((x) => Number.isNaN(x) || x === 0) },
  // atan2(y, x), from the steps of 21.3.2.8 that return a fixed value:
  // either argument NaN -> NaN; y is ±0 and (x > +0 or x is +0) -> y;
  // y finite and nonzero and x is +∞ -> +0 or -0 with the sign of y.
  // Every other step (including y = ±∞, y = ±0 with x < 0 or x = -0, and
  // finite nonzero y with x = -∞ or ±0) is implementation-approximated.
  atan2: {
    arity: 2,
    fn: Math.atan2,
    classify: (y, x) => {
      if (Number.isNaN(y) || Number.isNaN(x)) return 'exact';
      if (y === 0 && (x > 0 || Object.is(x, 0))) return 'exact';
      if (Number.isFinite(y) && y !== 0 && x === Infinity) return 'exact';
      return 'approximated';
    },
  },
  // hypot: any ±∞ -> +∞; then any NaN -> NaN; all ±0 -> +0.
  hypot: {
    arity: 'variadic',
    fn: Math.hypot,
    classify: (...xs) =>
      xs.some((v) => v === Infinity || v === -Infinity) || xs.some(Number.isNaN) || xs.every(isZero)
        ? 'exact'
        : 'approximated',
  },
  // pow: Number::exponentiate lists exact results for every case where an
  // operand is NaN, ±0, or ±∞, and for negative finite base with non-integral
  // finite exponent (NaN). The last step is implementation-approximated.
  pow: {
    arity: 2,
    fn: Math.pow,
    classify: (b, e) => {
      if (Number.isNaN(e) || Number.isNaN(b)) return 'exact';
      if (e === 0) return 'exact';
      if (!Number.isFinite(b) || b === 0 || !Number.isFinite(e)) return 'exact';
      if (b < 0 && !Number.isInteger(e)) return 'exact';
      return 'approximated';
    },
  },
};

function cross(xs) {
  const out = [];
  for (const a of xs) for (const b of xs) out.push([a, b]);
  return out;
}

function build() {
  const records = [];
  for (const name of Object.keys(MEMBERS).sort()) {
    const m = MEMBERS[name];
    const candidates =
      m.arity === 1
        ? UNARY.map((x) => [x])
        : [
            ...cross(BINARY_BASE),
            ...BINARY_COMMON,
            ...(BINARY_EXTRA[name] ?? []),
            ...(m.arity === 'variadic' ? VARIADIC : []),
          ];
    // Keep the first occurrence of each input tuple, compared by bit pattern
    // so that 0 and -0 stay distinct.
    const seen = new Set();
    const inputs = candidates.filter((args) => {
      const key = args.map(hex).join(',');
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
    for (const args of inputs) {
      const result = m.fn(...args);
      records.push({
        member: `Math.${name}`,
        inputs: args.map(value),
        result: value(result),
        class: m.classify(...args),
      });
    }
  }
  // `**` is Number::exponentiate, the same operation as Math.pow; recorded
  // separately for the operator form on a few defining cases.
  for (const [b, e] of [[1, NaN], [1, Infinity], [1, -Infinity], [-1, Infinity], [-1, -Infinity], [NaN, 0], [-0, -1], [0, -1]]) {
    records.push({
      member: '**',
      inputs: [value(b), value(e)],
      result: value(b ** e),
      class: MEMBERS.pow.classify(b, e),
    });
  }
  return {
    schema: 'lemmascript-math-vectors/1',
    generator: 'node spikes/math-semantics/vectors/gen.mjs',
    engine: { node: process.version, v8: process.versions.v8 },
    specEdition: SPEC_EDITION,
    note:
      'Results are what this engine returned. For records with class "approximated" the spec allows other engines or versions to return a different Number value.',
    records,
  };
}

// Pretty-print the header and put one record per line so diffs stay readable.
function serialize(doc) {
  const { records, ...header } = doc;
  const head = JSON.stringify(header, null, 2).replace(/\n}$/, '');
  const body = records.map((r) => '    ' + JSON.stringify(r)).join(',\n');
  return `${head},\n  "records": [\n${body}\n  ]\n}\n`;
}

const text = serialize(build());

if (process.argv.includes('--check')) {
  let committed;
  try {
    committed = readFileSync(outFile, 'utf8');
  } catch {
    console.error(`check: ${outFile} is missing`);
    process.exit(1);
  }
  if (committed !== text) {
    const a = committed.split('\n');
    const b = text.split('\n');
    const n = Math.max(a.length, b.length);
    for (let i = 0; i < n; i++) {
      if (a[i] !== b[i]) {
        console.error(`check: first difference at line ${i + 1}`);
        console.error(`  committed: ${a[i]}`);
        console.error(`  generated: ${b[i]}`);
        break;
      }
    }
    process.exit(1);
  }
  console.log(`check: ${outFile} matches (${JSON.parse(text).records.length} records)`);
} else {
  writeFileSync(outFile, text);
  console.log(`wrote ${outFile} (${JSON.parse(text).records.length} records)`);
}
