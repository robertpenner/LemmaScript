# AFK Run: LemmaScript JavaScript number support, research spikes (#23, #20)

**Status:** active

**Branch:** one worktree and spike branch per ticket, siblings of `LemmaScript/`; this log lives on `afk/numbers-2-log`. Spike branches never merge into fork `main`.

**Pull requests:** #23 in fork draft PR #28 (spike, not for merge); #20 not opened yet.

**Started:** 2026-11-19 14:49:43 UTC

**Goal:** Produce the evidence two #14 research tickets ask for: a backend-neutral `Math.*` semantics table with Node vectors and Lean divergence examples (#23), and a Dafny number-encoding spike answering `DESIGN_NUMBERS.md` §5 Questions 1 to 6 (#20).

**Execution:** parallel, 2 workers. Advisor and final reviewer: `gemini-4-carbon`.

**Verified integration head:** none yet.

### Slice progress

| Issue | Slice                           | Status      | Blocked by / reason | Integration commit | Verification |
| ----- | ------------------------------- | ----------- | ------------------- | ------------------ | ------------ |
| #23   | `Math.*` semantics table        | verified, draft PR #28 |              | `599ee04` (pushed) | gen `--check`, Lean compile, Dafny fixtures rerun by coordinator; Carbon review resolved |
| #20   | Dafny number-encoding spike     | in progress |                     |                    |              |

### Parallel workers

| Ticket | Checkout            | Branch                         | Starting verified SHA | Allowed files                     | Worker state |
| ------ | ------------------- | ------------------------------ | --------------------- | --------------------------------- | ------------ |
| #23    | `LemmaScript-ws-05` | `spike/math-semantics-table`   | `60cab87`             | new files in `spikes/math-semantics/` | done: `1562258`, review fixes `599ee04`; all files under `spikes/math-semantics/` |
| #20    | `LemmaScript-ws-06` | `spike/dafny-number-encodings` | `60cab87`             | new files in `spikes/dafny-number-encodings/` | running |

Briefs: [#23](https://github.com/robertpenner/LemmaScript/issues/23#issuecomment-7012742197), [#20](https://github.com/robertpenner/LemmaScript/issues/20#issuecomment-7012742694).

### Environment

- Node `v24.17.0`; pinned Dafny `4.11.0+fcb2042`; Lean `v4.34.0`; Mathlib cache fetched in ws-05 (`velvet` cloned at `22ed782` as the sibling `../velvet`, as CI does).
- Encoding C toolchain: Dafny nightly `4.11.1+a869244` (`nightly-2026-11-02-a869244`, arm64 macOS) unpacked in scratch; it verified a trivial `fp64` addition.
- Upstream status at start: dafny-lang/dafny#6323 merged 2025-11-07; dafny-lang/dafny#6514 open draft; boogie-org/boogie#1141 merged 2026-08-20.

### Verification evidence

#23 at `1562258`, rerun by the coordinator in ws-05:

- `node spikes/math-semantics/vectors/gen.mjs --check`: exit 0, "matches (1405 records)".
- `lake env lean spikes/math-semantics/lean/Divergences.lean`: exit 0; output is only `#check` and `#eval` results, no warnings, errors, or `sorry`. The worker reported "no output", which was inaccurate.
- `git diff --name-only 60cab87..1562258`: every path is under `spikes/math-semantics/`.
- `node spikes/math-semantics/fixtures/run-dafny-gen.mjs <scratch>`: 36 fixtures, 12 emitted. `dafny verify` (4.11.0): 10 exit 0 (`absInt` 1 verified; the other 9 have no contracts, 0 verified), `expOpInt` and `expOpReal` exit 2 with 1 parse error each.
- `cd tools && npm test`: not runnable, `tools/package.json` has no `test` script. Root `npm run typecheck` exit 0 (worker-reported).

#23 at `599ee04` (review fixes, 8 files, +253/-59), rerun by the coordinator in ws-05:

- `git diff --name-only 60cab87..599ee04`: every path is under `spikes/math-semantics/`.
- `node spikes/math-semantics/vectors/gen.mjs --check`: exit 0, "matches (1487 records)": 1014 exact, 473 approximated, no duplicate member and input tuples.
- `lake env lean spikes/math-semantics/lean/Divergences.lean`: exit 0, no warning, error, or `sorry` lines.
- New fixtures under `dafny verify` (4.11.0): `floorDivInt` 2 verified; `floorDivIntUnguarded` 1 error (precondition); `minSpreadInt` 1 error; `maxSpreadIntGuarded` 4 verified; `min3Int` rejected by `lsc gen`.
- `atan2(5e-324, 2)` record: result 0, class `approximated`.

Carbon review of `1562258` (`gemini-4-carbon`): confirmed clause ids, quotes, the 12/14 exact/approximated split, Lean line numbers and opaque/def claims, all vector records, and deterministic `--check`. Six findings, all fixed in `599ee04`:

1. "Verifies" wording for contract-free fixtures overstated the evidence; reworded to "0 verified, 0 errors".
2. The `atan2` classifier used the output `r === 0`; it now classifies by input, with subnormal pairs added.
3. Variadic `min`, `max`, and `hypot` vectors were missing; added.
4. The Dafny column omitted `JSFloorDiv`, the arity-2 limit, and `MinOfSeq`/`MaxOfSeq`; added with fixtures.
5. `pow`, `sign`, and `abs` special cases were incomplete; completed.
6. 16 duplicate vectors; removed.

#20: pending.

### Decisions

- Finding from #23: `lsc gen` emits `x ** y` unchanged and Dafny rejects the output with a parse error, although `SPEC.md` says `**` has no lowering. Candidate fork issue after the run.
- Finding from #23 review: `Math.floor(a / b)` lowers to `JSFloorDiv`, which matches JavaScript only while the quotient is exactly representable; `Math.floor(2 ** 60 / 3)` is 384307168202282304 in Node, the integer floor is 384307168202282325.
- Spike artifacts go under `spikes/<topic>/` with no edits to tracked files.
- #20's report answers the six questions in `DESIGN_NUMBERS.md` §5 verbatim, then maps the issue's own six topics onto them, because the two lists differ.
