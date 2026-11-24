#!/usr/bin/env node
// Standalone, emitter-independent Node DataView binary64 conformance oracle.
// Implements DESIGN_NUMBERS.md §§2, 7, and 8 Phase 0.3 (robertpenner/LemmaScript#19).
//
// Usage (from the repository root):
//   node spikes/binary64-oracle/oracle.mjs           write spikes/binary64-oracle/vectors.json
//   node spikes/binary64-oracle/oracle.mjs --check   regenerate and compare byte-for-byte, exit 1 on mismatch
//
// Deterministic: fixed boundary corpus, zero randomness, zero external network access.

import { readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';

const here = dirname(fileURLToPath(import.meta.url));
export const DEFAULT_OUT_FILE = join(here, 'vectors.json');

export const SCHEMA = 'lemmascript-binary64-oracle/1';
export const CANONICAL_NAN_HEX = '0x7ff8000000000000';
export const SPEC_EDITION =
  'ECMAScript 2026 Language Specification (https://tc39.es/ecma262/2026/multipage/)';
export const TEST262_PROVENANCE = {
  repository: 'https://github.com/tc39/test262',
  style: 'curated-self-contained',
  note:
    'Curated vectors cite TC39 Test262 paths and ECMAScript 2026 clauses without requiring a network checkout; replace or augment with direct Test262 extraction if upstream adopts a submodule.',
};

const _buf = new ArrayBuffer(8);
const _dv = new DataView(_buf);

/** Convert a JS Number to its big-endian 64-bit IEEE-754 hex string via DataView. */
export function rawHex(x) {
  _dv.setFloat64(0, x, false);
  return '0x' + _dv.getBigUint64(0, false).toString(16).padStart(16, '0');
}

/** Construct a JS Number from an exact 64-bit big-endian IEEE-754 hex string. */
export function fromHex(hexStr) {
  _dv.setBigUint64(0, BigInt(hexStr), false);
  return _dv.getFloat64(0, false);
}

/** Canonicalize all IEEE-754 NaN encodings to the single ECMAScript abstract NaN bit pattern. */
export function canonicalHex(x) {
  return Number.isNaN(x) ? CANONICAL_NAN_HEX : rawHex(x);
}

export function classifyNumber(x) {
  if (Number.isNaN(x)) return 'nan';
  if (x === Infinity) return 'pos-inf';
  if (x === -Infinity) return 'neg-inf';
  if (Object.is(x, -0)) return 'neg-zero';
  if (Object.is(x, 0)) return 'pos-zero';
  return 'finite';
}

export function jsLiteral(x) {
  if (Number.isNaN(x)) return 'NaN';
  if (x === Infinity) return 'Infinity';
  if (x === -Infinity) return '-Infinity';
  if (Object.is(x, -0)) return '-0';
  return String(x);
}

/**
 * Value representation aligned with fork #23's `lemmascript-math-vectors/1` (`{ js, hex }`),
 * adding `kind` for explicit special-value categorization. All NaN values are canonicalized
 * to `0x7ff8000000000000` in `hex`.
 */
export function encodeNumber(x) {
  return {
    js: jsLiteral(x),
    hex: canonicalHex(x),
    kind: classifyNumber(x),
  };
}

export function encodeBool(b) {
  return { bool: Boolean(b) };
}

// Boundary value corpus from DESIGN_NUMBERS.md §7 and robertpenner/LemmaScript#19.
export const LARGEST_SUBNORMAL = fromHex('0x000fffffffffffff');
export const SMALLEST_NORMAL = fromHex('0x0010000000000000'); // 2.2250738585072014e-308
export const HALF_MINUS_ULP = 0.49999999999999994; // 0.5 * (1 - Number.EPSILON / 2)

export const BOUNDARY_VALUES = [
  0,
  -0,
  NaN,
  Infinity,
  -Infinity,
  Number.MIN_VALUE,
  -Number.MIN_VALUE,
  LARGEST_SUBNORMAL,
  -LARGEST_SUBNORMAL,
  SMALLEST_NORMAL,
  -SMALLEST_NORMAL,
  Number.EPSILON,
  -Number.EPSILON,
  0.1,
  0.2,
  0.3,
  0.5,
  -0.5,
  HALF_MINUS_ULP,
  -HALF_MINUS_ULP,
  1,
  -1,
  1.5,
  -1.5,
  2,
  -2,
  2.5,
  -2.5,
  5,
  -5,
  2 ** 31 - 1,
  2 ** 31,
  -(2 ** 31),
  2 ** 32 - 1,
  2 ** 32,
  2 ** 53 - 1,
  2 ** 53,
  2 ** 53 + 2,
  -(2 ** 53 - 1),
  -(2 ** 53),
  -(2 ** 53 + 2),
  Number.MAX_VALUE,
  -Number.MAX_VALUE,
];

// Compact core subset for full Cartesian cross-products so the vector file stays readable and fast.
const CORE_PAIR_VALUES = [
  0,
  -0,
  NaN,
  Infinity,
  -Infinity,
  1,
  -1,
  0.5,
  -0.5,
  2,
  -2,
  Number.MIN_VALUE,
  Number.MAX_VALUE,
  2 ** 53 - 1,
  2 ** 53,
];

function dedupeTuples(tuples) {
  const seen = new Set();
  return tuples.filter((args) => {
    const key = args.map(canonicalHex).join(',');
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

function cross(xs, ys = xs) {
  const out = [];
  for (const a of xs) for (const b of ys) out.push([a, b]);
  return out;
}

function classifyPow(b, e) {
  if (Number.isNaN(e) || Number.isNaN(b)) return 'exact';
  if (e === 0) return 'exact';
  if (!Number.isFinite(b) || b === 0 || !Number.isFinite(e)) return 'exact';
  if (b < 0 && !Number.isInteger(e)) return 'exact';
  return 'approximated';
}

function sameValueZero(x, y) {
  const inArr = [x].includes(y);
  const inSet = new Set([x]).has(y);
  if (inArr !== inSet) {
    throw new Error(`SameValueZero mismatch between Array.includes and Set.has for ${jsLiteral(x)}, ${jsLiteral(y)}`);
  }
  return inArr;
}

function buildNanPayloadRecords() {
  // Distinct non-canonical quiet and signaling NaN bit patterns.
  const payloads = [
    { label: 'canonical-qnan', inputHex: '0x7ff8000000000000' },
    { label: 'positive-qnan-payload-1', inputHex: '0x7ff8000000000001' },
    { label: 'negative-qnan-payload-42', inputHex: '0xfff8000000000042' },
    { label: 'positive-snan-payload-1', inputHex: '0x7ff0000000000001' },
  ];
  const records = [];
  for (const { label, inputHex } of payloads) {
    const buf = new ArrayBuffer(8);
    const dv = new DataView(buf);
    dv.setBigUint64(0, BigInt(inputHex), false);
    const preservedRawHex = '0x' + dv.getBigUint64(0, false).toString(16).padStart(16, '0');
    const asNumber = dv.getFloat64(0, false);
    const sum = asNumber + 1;
    records.push({
      family: 'nan-payload',
      op: 'DataView.roundtrip',
      label,
      inputHex,
      preservedRawHex,
      asNumber: encodeNumber(asNumber),
      arithmeticPlusOne: encodeNumber(sum),
      isNaN: Number.isNaN(asNumber),
      strictEqSelf: asNumber === asNumber,
      objectIsCanonicalNaN: Object.is(asNumber, NaN),
      sameValueZeroCanonicalNaN: sameValueZero(asNumber, NaN),
      class: 'exact',
    });
  }
  // Computed NaN expressions must all canonicalize to CANONICAL_NAN_HEX.
  const computed = [
    { expr: '0 / 0', value: 0 / 0 },
    { expr: '-0 / 0', value: -0 / 0 },
    { expr: 'Infinity - Infinity', value: Infinity - Infinity },
    { expr: 'Infinity * 0', value: Infinity * 0 },
    { expr: 'Infinity / Infinity', value: Infinity / Infinity },
    { expr: '1 % 0', value: 1 % 0 },
  ];
  for (const { expr, value } of computed) {
    records.push({
      family: 'nan-payload',
      op: 'computed-nan',
      expr,
      result: encodeNumber(value),
      class: 'exact',
    });
  }
  return records;
}

function buildUnaryArithmeticRecords() {
  const records = [];
  for (const x of BOUNDARY_VALUES) {
    records.push({
      family: 'unary-arithmetic',
      op: 'unary-',
      inputs: [encodeNumber(x)],
      result: encodeNumber(-x),
      class: 'exact',
    });
    records.push({
      family: 'unary-arithmetic',
      op: 'unary+',
      inputs: [encodeNumber(x)],
      result: encodeNumber(+x),
      class: 'exact',
    });
  }
  return records;
}

function buildBinaryArithmeticRecords() {
  const targeted = [
    [-0, -0],
    [-0, 0],
    [0, -0],
    [-0, 5],
    [5, -0],
    [1, -0],
    [-1, -0],
    [-5, 5],
    [5, -5],
    [-5, -5],
    [0.1, 0.2],
    [0.3, 0.1],
    [2 ** 53, 1],
    [2 ** 53, 2],
    [2 ** 53 + 2, 1],
    [2 ** 53 - 1, 1],
    [2 ** 53 - 1, 2],
    [-(2 ** 53), -1],
    [-(2 ** 53), 1],
    [Number.MIN_VALUE, 2],
    [-Number.MIN_VALUE, 2],
    [1e-323, 4],
    [LARGEST_SUBNORMAL, Number.MIN_VALUE],
    [SMALLEST_NORMAL, Number.MIN_VALUE],
    [Number.MAX_VALUE, 2],
    [Number.MAX_VALUE, Number.MAX_VALUE],
    [-Number.MAX_VALUE, Number.MAX_VALUE],
    [1e16, 1],
    [1e16 + 2, 1e16],
    [HALF_MINUS_ULP, 0.5],
  ];
  const pairs = dedupeTuples([...cross(CORE_PAIR_VALUES), ...targeted]);
  const ops = [
    { op: '+', fn: (a, b) => a + b, classify: () => 'exact' },
    { op: '-', fn: (a, b) => a - b, classify: () => 'exact' },
    { op: '*', fn: (a, b) => a * b, classify: () => 'exact' },
    { op: '/', fn: (a, b) => a / b, classify: () => 'exact' },
    { op: '%', fn: (a, b) => a % b, classify: () => 'exact' },
  ];
  const records = [];
  for (const { op, fn, classify } of ops) {
    for (const [a, b] of pairs) {
      records.push({
        family: 'binary-arithmetic',
        op,
        inputs: [encodeNumber(a), encodeNumber(b)],
        result: encodeNumber(fn(a, b)),
        class: classify(a, b),
      });
    }
  }
  // Exact special-value matrix plus representative finite pairs for `**`.
  const powPairs = dedupeTuples([
    [1, NaN],
    [1, Infinity],
    [1, -Infinity],
    [-1, Infinity],
    [-1, -Infinity],
    [NaN, 0],
    [NaN, -0],
    [0, -1],
    [-0, -1],
    [-0, -2],
    [-0, -3],
    [-0, 2],
    [-0, 3],
    [0, 0],
    [-0, 0],
    [0.5, Infinity],
    [0.5, -Infinity],
    [2, Infinity],
    [2, -Infinity],
    [-2, 0.5],
    [-2, 3],
    [2, 53],
    [2, 1024],
    [2, -1075],
  ]);
  for (const [a, b] of powPairs) {
    records.push({
      family: 'binary-arithmetic',
      op: '**',
      inputs: [encodeNumber(a), encodeNumber(b)],
      result: encodeNumber(a ** b),
      class: classifyPow(a, b),
    });
  }
  // Catastrophic cancellation multi-step witness: (1e16 + 1) - 1e16 === 0 vs (1e16 + 2) - 1e16 === 2.
  records.push({
    family: 'binary-arithmetic',
    op: 'cancellation',
    expr: '(1e16 + 1) - 1e16',
    inputs: [encodeNumber(1e16), encodeNumber(1)],
    result: encodeNumber((1e16 + 1) - 1e16),
    class: 'exact',
  });
  records.push({
    family: 'binary-arithmetic',
    op: 'cancellation',
    expr: '(1e16 + 2) - 1e16',
    inputs: [encodeNumber(1e16), encodeNumber(2)],
    result: encodeNumber((1e16 + 2) - 1e16),
    class: 'exact',
  });
  return records;
}

function buildComparisonAndEqualityRecords() {
  const eqValues = [
    0,
    -0,
    NaN,
    Infinity,
    -Infinity,
    Number.MIN_VALUE,
    -Number.MIN_VALUE,
    1,
    -1,
    2 ** 53 - 1,
    2 ** 53,
    Number.MAX_VALUE,
  ];
  const pairs = dedupeTuples(cross(eqValues));
  const records = [];
  for (const [a, b] of pairs) {
    records.push({
      family: 'comparison-equality',
      op: 'compare-all',
      inputs: [encodeNumber(a), encodeNumber(b)],
      results: {
        lt: a < b,
        lte: a <= b,
        gt: a > b,
        gte: a >= b,
        strictEq: a === b,
        strictNeq: a !== b,
        objectIs: Object.is(a, b),
        sameValueZero: sameValueZero(a, b),
      },
      class: 'exact',
    });
  }
  for (const x of BOUNDARY_VALUES) {
    records.push({
      family: 'truthiness',
      op: 'Boolean',
      inputs: [encodeNumber(x)],
      result: encodeBool(Boolean(x)),
      class: 'exact',
    });
  }
  return records;
}

function buildBitwiseRecords() {
  const intBoundary = [
    0,
    -0,
    NaN,
    Infinity,
    -Infinity,
    0.5,
    -0.5,
    1.9,
    -1.9,
    1,
    -1,
    2 ** 31 - 1,
    2 ** 31,
    -(2 ** 31),
    -(2 ** 31) - 1,
    2 ** 32 - 1,
    2 ** 32,
    2 ** 32 + 1,
    2 ** 53 - 1,
    2 ** 53,
    2 ** 53 + 2,
    -(2 ** 53),
    Number.MAX_VALUE,
    Number.MIN_VALUE,
  ];
  const records = [];
  for (const x of intBoundary) {
    records.push({
      family: 'bitwise-conversion',
      op: 'ToInt32',
      inputs: [encodeNumber(x)],
      result: encodeNumber(x | 0),
      class: 'exact',
    });
    records.push({
      family: 'bitwise-conversion',
      op: 'ToUint32',
      inputs: [encodeNumber(x)],
      result: encodeNumber(x >>> 0),
      class: 'exact',
    });
    records.push({
      family: 'bitwise-unary',
      op: '~',
      inputs: [encodeNumber(x)],
      result: encodeNumber(~x),
      class: 'exact',
    });
  }
  const bitPairs = dedupeTuples([
    [0, 0],
    [-0, 0],
    [-1, 0],
    [-1, 1],
    [-1, 0xff],
    [0x55555555, 0xaaaaaaaa],
    [2 ** 31, 0],
    [2 ** 31 - 1, 1],
    [2 ** 32, 0],
    [2 ** 53 + 2, 0],
    [2 ** 53 - 1, 0xffffffff],
    [Infinity, 0],
    [-Infinity, 0],
    [NaN, 0],
    [NaN, -1],
  ]);
  for (const [a, b] of bitPairs) {
    for (const [op, fn] of [
      ['|', (x, y) => x | y],
      ['&', (x, y) => x & y],
      ['^', (x, y) => x ^ y],
    ]) {
      records.push({
        family: 'bitwise-binary',
        op,
        inputs: [encodeNumber(a), encodeNumber(b)],
        result: encodeNumber(fn(a, b)),
        class: 'exact',
      });
    }
  }
  const shiftPairs = dedupeTuples([
    [1, 0],
    [1, 1],
    [1, 31],
    [1, 32],
    [1, 33],
    [1, -1],
    [-1, 0],
    [-1, 1],
    [-1, 31],
    [-1, 32],
    [-1, 33],
    [2 ** 31, 1],
    [-(2 ** 31), 1],
    [2 ** 32 + 1, 0],
    [2 ** 53 + 2, 0],
    [Infinity, 1],
    [NaN, 1],
    [-0, 0],
  ]);
  for (const [a, b] of shiftPairs) {
    for (const [op, fn] of [
      ['<<', (x, y) => x << y],
      ['>>', (x, y) => x >> y],
      ['>>>', (x, y) => x >>> y],
    ]) {
      records.push({
        family: 'bitwise-shift',
        op,
        inputs: [encodeNumber(a), encodeNumber(b)],
        result: encodeNumber(fn(a, b)),
        class: 'exact',
      });
    }
  }
  return records;
}

function buildNumberPredicateRecords() {
  const preds = [
    ['Number.isNaN', Number.isNaN],
    ['Number.isFinite', Number.isFinite],
    ['Number.isInteger', Number.isInteger],
    ['Number.isSafeInteger', Number.isSafeInteger],
  ];
  const records = [];
  for (const [member, fn] of preds) {
    for (const x of BOUNDARY_VALUES) {
      records.push({
        family: 'number-predicate',
        member,
        inputs: [encodeNumber(x)],
        result: encodeBool(fn(x)),
        class: 'exact',
      });
    }
  }
  return records;
}

function buildMathDeterministicRecords() {
  const records = [];
  const unaryMembers = [
    ['Math.abs', Math.abs],
    ['Math.floor', Math.floor],
    ['Math.ceil', Math.ceil],
    ['Math.round', Math.round],
    ['Math.trunc', Math.trunc],
    ['Math.sign', Math.sign],
    ['Math.sqrt', Math.sqrt],
    ['Math.fround', Math.fround],
    ['Math.clz32', Math.clz32],
  ];
  for (const [member, fn] of unaryMembers) {
    for (const x of BOUNDARY_VALUES) {
      records.push({
        family: 'math-deterministic',
        member,
        inputs: [encodeNumber(x)],
        result: encodeNumber(fn(x)),
        class: 'exact',
      });
    }
  }

  const minMaxBase = [0, -0, NaN, Infinity, -Infinity, 1, -1, 0.5, -0.5, Number.MIN_VALUE, Number.MAX_VALUE];
  const minMaxPairs = dedupeTuples(cross(minMaxBase));
  const minMaxVariadic = [
    [],
    [NaN],
    [-0],
    [0],
    [Infinity],
    [-Infinity],
    [-5],
    [1, -0, 0],
    [-0, 0, -0],
    [1, NaN, Infinity],
    [Infinity, NaN, 1],
    [-Infinity, 1, 2],
  ];
  for (const [member, fn] of [
    ['Math.min', Math.min],
    ['Math.max', Math.max],
  ]) {
    for (const args of [...minMaxPairs, ...minMaxVariadic]) {
      records.push({
        family: 'math-deterministic',
        member,
        inputs: args.map(encodeNumber),
        result: encodeNumber(fn(...args)),
        class: 'exact',
      });
    }
  }

  const imulPairs = dedupeTuples([
    [0, 0],
    [-0, 5],
    [NaN, 5],
    [Infinity, 2],
    [2, 3],
    [-2, 3],
    [2 ** 31, 2],
    [4294967295, 5],
    [0xffffffff, 0xffffffff],
    [0xfffffffe, 5],
    [1.9, 3.9],
    [-1.9, 3.9],
  ]);
  for (const [a, b] of imulPairs) {
    records.push({
      family: 'math-deterministic',
      member: 'Math.imul',
      inputs: [encodeNumber(a), encodeNumber(b)],
      result: encodeNumber(Math.imul(a, b)),
      class: 'exact',
    });
  }

  return records;
}

function buildTest262CuratedRecords() {
  // Curated Test262 edge cases citing exact TC39 Test262 test paths and ECMAScript 2026 clauses.
  const cases = [
    {
      id: 't262-math-min-signed-zero',
      test262Path: 'test/built-ins/Math/min/S15.8.2.12_A1.js',
      clause: '21.3.2.25',
      op: 'Math.min(+0, -0)',
      inputs: [0, -0],
      result: encodeNumber(Math.min(0, -0)),
    },
    {
      id: 't262-math-max-signed-zero',
      test262Path: 'test/built-ins/Math/max/S15.8.2.11_A1.js',
      clause: '21.3.2.24',
      op: 'Math.max(-0, +0)',
      inputs: [-0, 0],
      result: encodeNumber(Math.max(-0, 0)),
    },
    {
      id: 't262-math-round-neg-half',
      test262Path: 'test/built-ins/Math/round/S15.8.2.15_A6.js',
      clause: '21.3.2.28',
      op: 'Math.round(-0.5)',
      inputs: [-0.5],
      result: encodeNumber(Math.round(-0.5)),
    },
    {
      id: 't262-math-round-half-minus-ulp',
      test262Path: 'test/built-ins/Math/round/round-half-minus-ulp.js',
      clause: '21.3.2.28',
      op: 'Math.round(0.49999999999999994)',
      inputs: [HALF_MINUS_ULP],
      result: encodeNumber(Math.round(HALF_MINUS_ULP)),
    },
    {
      id: 't262-math-trunc-neg-half',
      test262Path: 'test/built-ins/Math/trunc/trunc-specialVals.js',
      clause: '21.3.2.35',
      op: 'Math.trunc(-0.5)',
      inputs: [-0.5],
      result: encodeNumber(Math.trunc(-0.5)),
    },
    {
      id: 't262-math-sqrt-neg-zero',
      test262Path: 'test/built-ins/Math/sqrt/S15.8.2.17_A5.js',
      clause: '21.3.2.32',
      op: 'Math.sqrt(-0)',
      inputs: [-0],
      result: encodeNumber(Math.sqrt(-0)),
    },
    {
      id: 't262-object-is-signed-zero',
      test262Path: 'test/built-ins/Object/is/not-same-value-x-y-zero.js',
      clause: '7.2.10',
      op: 'Object.is(+0, -0)',
      inputs: [0, -0],
      result: encodeBool(Object.is(0, -0)),
    },
    {
      id: 't262-object-is-nan',
      test262Path: 'test/built-ins/Object/is/same-value-x-y-nan.js',
      clause: '7.2.10',
      op: 'Object.is(NaN, NaN)',
      inputs: [NaN, NaN],
      result: encodeBool(Object.is(NaN, NaN)),
    },
    {
      id: 't262-number-is-safe-integer-neg-zero',
      test262Path: 'test/built-ins/Number/isSafeInteger/safe-integers.js',
      clause: '21.1.2.5',
      op: 'Number.isSafeInteger(-0)',
      inputs: [-0],
      result: encodeBool(Number.isSafeInteger(-0)),
    },
    {
      id: 't262-number-is-safe-integer-boundary',
      test262Path: 'test/built-ins/Number/isSafeInteger/not-safe-integer.js',
      clause: '21.1.2.5',
      op: 'Number.isSafeInteger(2**53)',
      inputs: [2 ** 53],
      result: encodeBool(Number.isSafeInteger(2 ** 53)),
    },
    {
      id: 't262-ties-to-even-2pow53-plus-1',
      test262Path: 'test/language/expressions/addition/S11.6.1_A4_T1.js',
      clause: '6.1.6.1.7',
      op: '(2 ** 53) + 1',
      inputs: [2 ** 53, 1],
      result: encodeNumber(2 ** 53 + 1),
    },
    {
      id: 't262-rem-neg-multiple-sign',
      test262Path: 'test/language/expressions/modulus/S11.5.3_A4_T6.js',
      clause: '6.1.6.1.6',
      op: '-5 % 5',
      inputs: [-5, 5],
      result: encodeNumber(-5 % 5),
    },
    {
      id: 't262-ushr-neg-one',
      test262Path: 'test/language/expressions/unsigned-right-shift/S11.7.3_A3_T1.1.js',
      clause: '6.1.6.1.11',
      op: '-1 >>> 0',
      inputs: [-1, 0],
      result: encodeNumber(-1 >>> 0),
    },
    {
      id: 't262-lshift-mask-32',
      test262Path: 'test/language/expressions/left-shift/S11.7.1_A3_T1.1.js',
      clause: '6.1.6.1.9',
      op: '1 << 32',
      inputs: [1, 32],
      result: encodeNumber(1 << 32),
    },
    {
      id: 't262-toint32-above-2pow53',
      test262Path: 'test/language/expressions/bitwise-or/S11.10.3_A3_T1.1.js',
      clause: '7.1.6',
      op: '(2**53 + 2) | 0',
      inputs: [2 ** 53 + 2, 0],
      result: encodeNumber((2 ** 53 + 2) | 0),
    },
    {
      id: 't262-pow-one-nan',
      test262Path: 'test/language/expressions/exponentiation/exp-operator-evaluation-order.js',
      clause: '6.1.6.1.3',
      op: '1 ** NaN',
      inputs: [1, NaN],
      result: encodeNumber(1 ** NaN),
    },
  ];
  return cases.map((c) => ({
    family: 'test262-curated',
    id: c.id,
    test262Path: c.test262Path,
    clause: c.clause,
    op: c.op,
    inputs: c.inputs.map(encodeNumber),
    result: c.result,
    class: 'exact',
  }));
}

export function buildOracleDocument() {
  const records = [
    ...buildNanPayloadRecords(),
    ...buildUnaryArithmeticRecords(),
    ...buildBinaryArithmeticRecords(),
    ...buildComparisonAndEqualityRecords(),
    ...buildBitwiseRecords(),
    ...buildNumberPredicateRecords(),
    ...buildMathDeterministicRecords(),
    ...buildTest262CuratedRecords(),
  ];

  const familyCounts = {};
  for (const r of records) {
    familyCounts[r.family] = (familyCounts[r.family] ?? 0) + 1;
  }

  return {
    schema: SCHEMA,
    generator: 'node spikes/binary64-oracle/oracle.mjs',
    engine: { node: process.version, v8: process.versions.v8 },
    specEdition: SPEC_EDITION,
    test262: TEST262_PROVENANCE,
    canonicalNaNHex: CANONICAL_NAN_HEX,
    boundaryCount: BOUNDARY_VALUES.length,
    recordCount: records.length,
    familyCounts,
    records,
  };
}

export function serializeOracleDocument(doc) {
  const { records, ...header } = doc;
  const head = JSON.stringify(header, null, 2).replace(/\n}$/, '');
  const body = records.map((r) => '    ' + JSON.stringify(r)).join(',\n');
  return `${head},\n  "records": [\n${body}\n  ]\n}\n`;
}

// Run CLI only when invoked directly.
if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const outIdx = process.argv.indexOf('--out');
  const outFile = outIdx >= 0 && process.argv[outIdx + 1] ? process.argv[outIdx + 1] : DEFAULT_OUT_FILE;
  const doc = buildOracleDocument();
  const text = serializeOracleDocument(doc);

  if (process.argv.includes('--check')) {
    let committed;
    try {
      committed = readFileSync(outFile, 'utf8');
    } catch {
      console.error(`check: ${outFile} is missing`);
      process.exit(1);
    }
    if (committed !== text) {
      console.error(`check: ${outFile} does not match regenerated output (run node spikes/binary64-oracle/oracle.mjs)`);
      process.exit(1);
    }
    console.log(`check: ${outFile} matches (${doc.recordCount} records across ${Object.keys(doc.familyCounts).length} families)`);
    process.exit(0);
  }

  writeFileSync(outFile, text);
  console.log(`wrote ${outFile} (${doc.recordCount} records across ${Object.keys(doc.familyCounts).length} families)`);
}
