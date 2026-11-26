# Binary64 Conformance Oracle (`DESIGN_NUMBERS.md` Phase 0.3)

Standalone, emitter-independent Node `DataView` conformance oracle and boundary corpus for
[`robertpenner/LemmaScript#19`](https://github.com/robertpenner/LemmaScript/issues/19), aligned with
[`DESIGN_NUMBERS.md`](../../DESIGN_NUMBERS.md) §§2, 7, and 8 Phase 0.3.

> **Layout note (`needs-info`):** Upstream `midspiral/LemmaScript` has not yet chosen the permanent directory path
> (`tools/number-oracle/` vs. `tools/tests/`) or Test262 packaging style (curated self-contained table vs. external
> checkout). Everything here lives self-contained under `spikes/binary64-oracle/` with zero edits outside this
> directory so it can be moved unchanged once upstream decides.

## Contents

```text
spikes/binary64-oracle/
├── README.md              # Schema, provenance, usage, and relocation notes
├── oracle.mjs             # Deterministic Node DataView oracle + --check verification
├── vectors.json           # Generated deterministic corpus (schema: lemmascript-binary64-oracle/1)
├── oracle.test.mjs        # Node test suite checking #19 acceptance criteria
└── crosscheck-dafny.mjs   # Cross-checks oracle vectors against fork #28 Math vectors and #29 Dafny Encoding B
```

## Schema (`lemmascript-binary64-oracle/1`)

Numeric values reuse the `{ js, hex }` fields from fork `#23` (`lemmascript-math-vectors/1`, PR `#28`) and add an
explicit `kind` tag (`"finite" | "pos-zero" | "neg-zero" | "pos-inf" | "neg-inf" | "nan"`):

- `hex`: big-endian 64-bit IEEE-754 hex pattern from `DataView.getBigUint64`, with all `NaN` outputs canonicalized to
  `0x7ff8000000000000` (ECMAScript's single abstract `NaN`).
- `-0` is `0x8000000000000000` (`kind: "neg-zero"`); `+0` is `0x0000000000000000` (`kind: "pos-zero"`).
- The `nan-payload` family separately tests raw `DataView` preservation (`preservedRawHex`) of distinct quiet and
  signaling `NaN` bit patterns (`0x7ff8000000000001`, `0xfff8000000000042`, `0x7ff0000000000001`) alongside their
  canonicalized observable behavior under arithmetic, `===`, `Object.is`, and `SameValueZero`.
- Every record carries `class: "exact" | "approximated"` following ECMAScript 2026: only non-special finite `**` pairs
  are marked `"approximated"`; all other families in this corpus are deterministic (`"exact"`).

## Operation families

1. `nan-payload`: Raw `DataView` payload round-trips and computed `NaN` canonicalization (`0 / 0`, `Infinity - Infinity`,
   `Infinity * 0`, `1 % 0`).
2. `unary-arithmetic`: Unary `-` and `+` across all 43 boundary values.
3. `binary-arithmetic`: `+`, `-`, `*`, `/`, `%`, `**`, plus rounding (`(2 ** 53) + 1`), subnormal underflow
   (`Number.MIN_VALUE / 2`, `1e-323 / 4`), overflow (`Number.MAX_VALUE * 2`), signed-zero rules (`-0 + -0`, `-0 + +0`,
   `-0 * 5`, `1 / -0`, `-5 % 5`), and catastrophic cancellation (`(1e16 + 1) - 1e16`).
4. `comparison-equality` and `truthiness`: `<`, `<=`, `>`, `>=`, `===`, `!==`, `Object.is`, `SameValueZero` (verified
   against both `Array.prototype.includes` and `Set.prototype.has`), and `Boolean(x)`.
5. `bitwise-conversion`, `bitwise-unary`, `bitwise-binary`, `bitwise-shift`: `ToInt32`, `ToUint32`, `~`, `|`, `&`, `^`,
   `<<`, `>>`, `>>>`, including shift-count masking modulo 32 and wraparound on `>= 2^53`, `NaN`, and `±Infinity`.
6. `number-predicate`: `Number.isNaN`, `Number.isFinite`, `Number.isInteger`, `Number.isSafeInteger`.
7. `math-deterministic`: `Math.abs`, `Math.min`, `Math.max` (0, 1, 2, 3 args), `Math.floor`, `Math.ceil`, `Math.round`,
   `Math.trunc`, `Math.sign`, `Math.sqrt`, `Math.fround`, `Math.imul`, `Math.clz32`.
8. `test262-curated`: Curated edge cases citing TC39 Test262 paths and ECMAScript 2026 clause IDs.

## Usage

Run from the repository root (zero external dependencies, zero network access):

```sh
# Regenerate vectors.json
node spikes/binary64-oracle/oracle.mjs

# Verify committed vectors.json matches regenerated output byte-for-byte
node spikes/binary64-oracle/oracle.mjs --check

# Run the oracle acceptance test suite
node --test spikes/binary64-oracle/oracle.test.mjs

# Optional: cross-check against fork #23 Math vectors and fork #20 Dafny Encoding B
node spikes/binary64-oracle/crosscheck-dafny.mjs \
  --math-vectors /path/to/spikes/math-semantics/vectors/math-special-values.json \
  --dafny-spike /path/to/spikes/dafny-number-encodings
```
