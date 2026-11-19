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
| #23   | `Math.*` semantics table        | in progress |                     |                    |              |
| #20   | Dafny number-encoding spike     | in progress |                     |                    |              |

### Parallel workers

| Ticket | Checkout            | Branch                         | Starting verified SHA | Allowed files                     | Worker state |
| ------ | ------------------- | ------------------------------ | --------------------- | --------------------------------- | ------------ |
| #23    | `LemmaScript-ws-05` | `spike/math-semantics-table`   | `60cab87`             | new files in `spikes/math-semantics/` | running |
| #20    | `LemmaScript-ws-06` | `spike/dafny-number-encodings` | `60cab87`             | new files in `spikes/dafny-number-encodings/` | running |

Briefs: [#23](https://github.com/robertpenner/LemmaScript/issues/23#issuecomment-7012742197), [#20](https://github.com/robertpenner/LemmaScript/issues/20#issuecomment-7012742694).

### Environment

- Node `v24.17.0`; pinned Dafny `4.11.0+fcb2042`; Lean `v4.34.0`; Mathlib cache fetched in ws-05 (`velvet` cloned at `22ed782` as the sibling `../velvet`, as CI does).
- Encoding C toolchain: Dafny nightly `4.11.1+a869244` (`nightly-2026-11-02-a869244`, arm64 macOS) unpacked in scratch; it verified a trivial `fp64` addition.
- Upstream status at start: dafny-lang/dafny#6323 merged 2025-11-07; dafny-lang/dafny#6514 open draft; boogie-org/boogie#1141 merged 2026-08-20.

### Verification evidence

Pending.

### Decisions

- Spike artifacts go under `spikes/<topic>/` with no edits to tracked files.
- #20's report answers the six questions in `DESIGN_NUMBERS.md` §5 verbatim, then maps the issue's own six topics onto them, because the two lists differ.
