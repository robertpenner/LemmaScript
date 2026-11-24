import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  CANONICAL_NAN_HEX,
  DEFAULT_OUT_FILE,
  HALF_MINUS_ULP,
  LARGEST_SUBNORMAL,
  SCHEMA,
  SMALLEST_NORMAL,
  buildOracleDocument,
  canonicalHex,
  encodeNumber,
  fromHex,
  rawHex,
  serializeOracleDocument,
} from './oracle.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const oracleScript = join(here, 'oracle.mjs');

test('oracle --check verifies committed vectors.json deterministically', () => {
  const res = spawnSync(process.execPath, [oracleScript, '--check'], { encoding: 'utf8' });
  assert.ifError(res.error);
  assert.equal(res.status, 0, res.stdout + res.stderr);
  assert.match(res.stdout, /matches \(\d+ records across \d+ families\)/);

  const committed = readFileSync(DEFAULT_OUT_FILE, 'utf8');
  const regenerated = serializeOracleDocument(buildOracleDocument());
  assert.equal(committed, regenerated);
});

test('provenance header records schema, engine versions, spec edition, and Test262 metadata', () => {
  const doc = JSON.parse(readFileSync(DEFAULT_OUT_FILE, 'utf8'));
  assert.equal(doc.schema, SCHEMA);
  assert.equal(doc.canonicalNaNHex, CANONICAL_NAN_HEX);
  assert.equal(doc.engine.node, process.version);
  assert.equal(doc.engine.v8, process.versions.v8);
  assert.match(doc.specEdition, /ECMAScript 2026/);
  assert.equal(doc.test262.style, 'curated-self-contained');
  assert.equal(doc.recordCount, doc.records.length);
  assert.ok(doc.records.length > 1000, `expected > 1000 records, got ${doc.records.length}`);
});

test('DataView distinguishes -0 from +0, subnormals from normals, and preserves raw NaN payloads', () => {
  assert.deepEqual(encodeNumber(0), { js: '0', hex: '0x0000000000000000', kind: 'pos-zero' });
  assert.deepEqual(encodeNumber(-0), { js: '-0', hex: '0x8000000000000000', kind: 'neg-zero' });
  assert.equal(rawHex(LARGEST_SUBNORMAL), '0x000fffffffffffff');
  assert.equal(rawHex(SMALLEST_NORMAL), '0x0010000000000000');
  assert.equal(rawHex(Number.MIN_VALUE), '0x0000000000000001');
  assert.equal(rawHex(Number.MAX_VALUE), '0x7fefffffffffffff');

  const doc = JSON.parse(readFileSync(DEFAULT_OUT_FILE, 'utf8'));
  const nanPayloads = doc.records.filter((r) => r.family === 'nan-payload' && r.op === 'DataView.roundtrip');
  assert.equal(nanPayloads.length, 4);
  for (const r of nanPayloads) {
    assert.equal(r.preservedRawHex, r.inputHex, `raw DataView roundtrip must preserve ${r.label}`);
    assert.equal(r.asNumber.hex, CANONICAL_NAN_HEX);
    assert.equal(r.arithmeticPlusOne.hex, CANONICAL_NAN_HEX);
    assert.equal(r.isNaN, true);
    assert.equal(r.strictEqSelf, false);
    assert.equal(r.objectIsCanonicalNaN, true);
    assert.equal(r.sameValueZeroCanonicalNaN, true);
  }
  const customNaN = fromHex('0xfff8000000000042');
  assert.equal(canonicalHex(customNaN), CANONICAL_NAN_HEX);
});

test('key #19 acceptance vectors are present with exact expected bits and booleans', () => {
  const doc = JSON.parse(readFileSync(DEFAULT_OUT_FILE, 'utf8'));

  const findMath = (member, inputHexes) =>
    doc.records.find(
      (r) =>
        r.family === 'math-deterministic' &&
        r.member === member &&
        r.inputs.length === inputHexes.length &&
        r.inputs.every((v, i) => v.hex === inputHexes[i]),
    );

  // Math.min(+0, -0) -> -0, Math.max(-0, +0) -> +0
  const minSignedZero = findMath('Math.min', ['0x0000000000000000', '0x8000000000000000']);
  assert.ok(minSignedZero);
  assert.equal(minSignedZero.result.hex, '0x8000000000000000');
  assert.equal(minSignedZero.result.kind, 'neg-zero');

  const maxSignedZero = findMath('Math.max', ['0x8000000000000000', '0x0000000000000000']);
  assert.ok(maxSignedZero);
  assert.equal(maxSignedZero.result.hex, '0x0000000000000000');
  assert.equal(maxSignedZero.result.kind, 'pos-zero');

  // Math.round(-0.5) -> -0; Math.round(0.49999999999999994) -> +0
  const roundNegHalf = findMath('Math.round', [canonicalHex(-0.5)]);
  assert.ok(roundNegHalf);
  assert.equal(roundNegHalf.result.hex, '0x8000000000000000');

  const roundHalfMinusUlp = findMath('Math.round', [canonicalHex(HALF_MINUS_ULP)]);
  assert.ok(roundHalfMinusUlp);
  assert.equal(roundHalfMinusUlp.result.hex, '0x0000000000000000');

  // (2 ** 53) + 1 === 2 ** 53 (ties-to-even)
  const addBoundary = doc.records.find(
    (r) =>
      r.family === 'binary-arithmetic' &&
      r.op === '+' &&
      r.inputs[0].hex === canonicalHex(2 ** 53) &&
      r.inputs[1].hex === canonicalHex(1),
  );
  assert.ok(addBoundary);
  assert.equal(addBoundary.result.hex, canonicalHex(2 ** 53));

  // Subnormal underflow: 1e-323 / 4 === +0 (Penner #4989)
  const underflow = doc.records.find(
    (r) =>
      r.family === 'binary-arithmetic' &&
      r.op === '/' &&
      r.inputs[0].hex === canonicalHex(1e-323) &&
      r.inputs[1].hex === canonicalHex(4),
  );
  assert.ok(underflow);
  assert.equal(underflow.result.hex, '0x0000000000000000');

  // -5 % 5 === -0
  const remNeg = doc.records.find(
    (r) =>
      r.family === 'binary-arithmetic' &&
      r.op === '%' &&
      r.inputs[0].hex === canonicalHex(-5) &&
      r.inputs[1].hex === canonicalHex(5),
  );
  assert.ok(remNeg);
  assert.equal(remNeg.result.hex, '0x8000000000000000');

  // Bitwise ToInt32 / ToUint32 / shift masking
  const toInt32Big = doc.records.find(
    (r) => r.family === 'bitwise-conversion' && r.op === 'ToInt32' && r.inputs[0].hex === canonicalHex(2 ** 53 + 2),
  );
  assert.ok(toInt32Big);
  assert.equal(toInt32Big.result.js, '2');

  const toInt32Inf = doc.records.find(
    (r) => r.family === 'bitwise-conversion' && r.op === 'ToInt32' && r.inputs[0].kind === 'pos-inf',
  );
  assert.ok(toInt32Inf);
  assert.equal(toInt32Inf.result.hex, '0x0000000000000000');

  const toUint32NegOne = doc.records.find(
    (r) => r.family === 'bitwise-conversion' && r.op === 'ToUint32' && r.inputs[0].hex === canonicalHex(-1),
  );
  assert.ok(toUint32NegOne);
  assert.equal(toUint32NegOne.result.js, '4294967295');

  const lshift32 = doc.records.find(
    (r) =>
      r.family === 'bitwise-shift' &&
      r.op === '<<' &&
      r.inputs[0].hex === canonicalHex(1) &&
      r.inputs[1].hex === canonicalHex(32),
  );
  assert.ok(lshift32);
  assert.equal(lshift32.result.js, '1');

  // Three distinct equality relations on (+0, -0) and (NaN, NaN)
  const eqZeros = doc.records.find(
    (r) =>
      r.family === 'comparison-equality' &&
      r.inputs[0].kind === 'pos-zero' &&
      r.inputs[1].kind === 'neg-zero',
  );
  assert.ok(eqZeros);
  assert.equal(eqZeros.results.strictEq, true);
  assert.equal(eqZeros.results.sameValueZero, true);
  assert.equal(eqZeros.results.objectIs, false);

  const eqNaNs = doc.records.find(
    (r) => r.family === 'comparison-equality' && r.inputs[0].kind === 'nan' && r.inputs[1].kind === 'nan',
  );
  assert.ok(eqNaNs);
  assert.equal(eqNaNs.results.strictEq, false);
  assert.equal(eqNaNs.results.sameValueZero, true);
  assert.equal(eqNaNs.results.objectIs, true);

  // Number.isSafeInteger(-0) === true, Number.isSafeInteger(2**53) === false
  const safeNegZero = doc.records.find(
    (r) =>
      r.family === 'number-predicate' &&
      r.member === 'Number.isSafeInteger' &&
      r.inputs[0].kind === 'neg-zero',
  );
  assert.ok(safeNegZero);
  assert.equal(safeNegZero.result.bool, true);

  const safe2pow53 = doc.records.find(
    (r) =>
      r.family === 'number-predicate' &&
      r.member === 'Number.isSafeInteger' &&
      r.inputs[0].hex === canonicalHex(2 ** 53),
  );
  assert.ok(safe2pow53);
  assert.equal(safe2pow53.result.bool, false);
});
