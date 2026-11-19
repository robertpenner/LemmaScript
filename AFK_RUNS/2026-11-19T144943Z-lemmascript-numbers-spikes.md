# AFK Run: LemmaScript JavaScript number support, research spikes (#23, #20)

**Status:** active

**Branch:** one worktree and spike branch per ticket, siblings of `LemmaScript/`; this log lives on `afk/numbers-2-log`. Spike branches never merge into fork `main`.

**Pull request:** not opened yet.

**Started:** 2026-11-19 14:49:43 UTC

**Goal:** Produce the evidence two #14 research tickets ask for: a backend-neutral `Math.*` semantics table with Node vectors and Lean divergence examples (#23), and a Dafny number-encoding spike answering `DESIGN_NUMBERS.md` §5 Questions 1 to 6 (#20).

**Execution:** parallel, 2 workers. Advisor and final reviewer: `gemini-4-carbon`.

**Verified integration head:** none yet.

### Slice progress

| Issue | Slice                           | Status      | Blocked by / reason | Integration commit | Verification |
| ----- | ------------------------------- | ----------- | ------------------- | ------------------ | ------------ |
| #23   | `Math.*` semantics table        | worker done, in review |               | `1562258` (unpushed) | gen `--check`, Lean compile, Dafny fixtures rerun by coordinator |
| #20   | Dafny number-encoding spike     | in progress |                     |                    |              |

### Parallel workers

| Ticket | Checkout            | Branch                         | Starting verified SHA | Allowed files                     | Worker state |
| ------ | ------------------- | ------------------------------ | --------------------- | --------------------------------- | ------------ |
| #23    | `LemmaScript-ws-05` | `spike/math-semantics-table`   | `60cab87`             | new files in `spikes/math-semantics/` | returned `1562258` (41 files, all under `spikes/math-semantics/`) |
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

#20: pending.

### Decisions

- Finding from #23: `lsc gen` emits `x ** y` unchanged and Dafny rejects the output with a parse error, although `SPEC.md` says `**` has no lowering. Candidate fork issue after the run.
- Spike artifacts go under `spikes/<topic>/` with no edits to tracked files.
- #20's report answers the six questions in `DESIGN_NUMBERS.md` §5 verbatim, then maps the issue's own six topics onto them, because the two lists differ.
