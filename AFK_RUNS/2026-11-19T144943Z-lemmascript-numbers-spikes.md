# AFK Run: LemmaScript JavaScript number support, research spikes (#23, #20)

**Status:** completed

**Branch:** one worktree and spike branch per ticket, siblings of `LemmaScript/`; this log lives on `afk/numbers-2-log`. Spike branches never merge into fork `main`.

**Pull requests:** #23 in fork draft PR #28, #20 in fork draft PR #29 (both spikes, not for merge).

**Started:** 2026-11-19 14:49:43 UTC

**Goal:** Produce the evidence two #14 research tickets ask for: a backend-neutral `Math.*` semantics table with Node vectors and Lean divergence examples (#23), and a Dafny number-encoding spike answering `DESIGN_NUMBERS.md` §5 Questions 1 to 6 (#20).

**Execution:** parallel, 2 workers. Advisor and per-ticket reviewer: `gemini-4-carbon`.

**Verified integration heads:** #23 `599ee04` on `spike/math-semantics-table`; #20 `6005100` on `spike/dafny-number-encodings`.

### Slice progress

| Issue | Slice                           | Status      | Blocked by / reason | Integration commit | Verification |
| ----- | ------------------------------- | ----------- | ------------------- | ------------------ | ------------ |
| #23   | `Math.*` semantics table        | verified, draft PR #28 |              | `599ee04` (pushed) | gen `--check`, Lean compile, Dafny fixtures rerun by coordinator; Carbon review resolved |
| #20   | Dafny number-encoding spike     | verified, draft PR #29 |              | `6005100` (pushed) | full `run.sh` rerun by coordinator; REPORT totals checked against `results/`; Carbon review resolved |

### Parallel workers

| Ticket | Checkout            | Branch                         | Starting verified SHA | Allowed files                     | Worker state |
| ------ | ------------------- | ------------------------------ | --------------------- | --------------------------------- | ------------ |
| #23    | `LemmaScript-ws-05` | `spike/math-semantics-table`   | `60cab87`             | new files in `spikes/math-semantics/` | done: `1562258`, review fixes `599ee04`; all files under `spikes/math-semantics/` |
| #20    | `LemmaScript-ws-06` | `spike/dafny-number-encodings` | `60cab87`             | new files in `spikes/dafny-number-encodings/` | done: `6332c3d`, `22ef1b1`, `8ac8174`; review fixes `2baaab6`, `c1278f1`, `6005100`; all files under `spikes/dafny-number-encodings/` |

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

#20 at `8ac8174` (174 files, all under `spikes/dafny-number-encodings/`), checked by the coordinator in ws-06:

- `git diff --name-only 60cab87..8ac8174`: 0 paths outside `spikes/dafny-number-encodings/`.
- `REPORT.md` answers the six `DESIGN_NUMBERS.md` §5 questions verbatim, maps the six issue topics, and says it "does not recommend an encoding".
- `DAFNY_FP=<nightly> VECTORS=<ws-05 json> ./run.sh`: exit 0. Every exit code, `js.csv`, `vectors.csv`, and repro classification matched the worker's run. Six rows near the 30 s time limit differed (verified/errors/timeouts, worker then rerun): A_safeint seed 3 6/0/1 vs 6/1/0; A_bitwise seed 2 11/1/2 vs 11/0/3; B_safeint seeds 1 and 2 17/0/1 vs 18/0/0; C_bitwise isolated 29/1/11 vs 29/2/10; R12 on Z3 4.12.1 3/1/1 vs 3/0/2. The REPORT's claim that B_safeint `Midpoint` times out under seeds 1 and 2 did not hold in the rerun.

Carbon review of `8ac8174` (`gemini-4-carbon`): confirmed every per-file count, isolated fraction, error citation, repro outcome, `-t js` exit code and vector count against `results/`, the §5 mapping, neutral wording, no `assume`/`{:axiom}`/`{:verify false}`/`{:extern}`, and the JavaScript semantics of A_lib, B_lib and C_lib against Node. Ten findings, sent to the worker with the rerun variance and fixed in `2baaab6`, `c1278f1`, `6005100`:

1. R07 left a zero dividend reachable, so `ByNegZero` failed on the 0/0 check; both methods now require a finite nonzero dividend.
2. `tagcount` matched the convention prose in `A_lib.dfy`, and `@lemma` mixed target and helper lemmas; now anchored, split into `@helper` and `@target`.
3. `run.sh` deleted committed vector results when `VECTORS` was unset; the vectors are vendored with provenance and used by default.
4. W1, W4 and W5 obligations differed across encodings; aligned, with failing aligned C proofs kept as data.
5. The R11 row named two of its three lemmas.
6. `head -40` cut R14's output before its summary line; only outputs without the summary line are truncated now.
7. Portability: Z3 glob, `nproc`/`sha256sum` fallbacks, preflight checks, relative paths.
8. to 10. Wording: OrZero(NaN) is an incomplete proof, `ObjectIsIsIdentity` states `x == y`, corrections split from the brief's own.

#20 at `6005100`, checked by the coordinator in ws-06:

- `git diff --name-only 8ac8174..6005100`: 0 paths outside `spikes/dafny-number-encodings/`; `git status --short` empty.
- Worker full run `DAFNY_FP=<nightly> ./run.sh` with the vendored vectors: exit 0.
- `grep -rl /Users/ results`: no files.
- `results/repro/R07_DivideByNegZero.nightly-z3-4.16.0.out`: one error, "possible division by zero" at (19,9) in `ByPosZero`; "7 verified, 1 error".
- Sums of the isolated rows in `results/summary.csv`: A 191/1/3, B 528/0/4, C 200/7/58; hints (`@manual` + `@helper`) A 14, B 51, C 16, matching the REPORT table.
- REPORT "Run-to-run variance" current column matches `results/summary.csv` and `results/repro.csv` (spot-checked A_bitwise seed 2, B_safeint seed 2, C_bitwise isolated, R12, R14).
- Corpus, repro, js and vector `.dfy` files: 0 matches for `assume`, `{:axiom`, `{:verify false`, `{:extern`.

### Decisions

- Finding from #23: `lsc gen` emits `x ** y` unchanged and Dafny rejects the output with a parse error, although `SPEC.md` says `**` has no lowering. Candidate fork issue after the run.
- Finding from #23 review: `Math.floor(a / b)` lowers to `JSFloorDiv`, which matches JavaScript only while the quotient is exactly representable; `Math.floor(2 ** 60 / 3)` is 384307168202282304 in Node, the integer floor is 384307168202282325.
- Spike artifacts go under `spikes/<topic>/` with no edits to tracked files.
- #20's report answers the six questions in `DESIGN_NUMBERS.md` §5 verbatim, then maps the issue's own six topics onto them, because the two lists differ.
- No separate final series `code-review`. The two spike branches are independent, share no files, and never merge; each received its own Carbon review against its brief, with every finding resolved and rechecked by the coordinator.

### Final verification

- #23 at `599ee04`: `node spikes/math-semantics/gen.mjs --check` exit 0 (coordinator rerun in ws-05).
- #20 at `6005100`: `DAFNY_FP=<nightly dafny> ./run.sh` exit 0 with the vendored vectors (worker run; coordinator rerun of `8ac8174` also exit 0).
- `gh pr checks 28` and `gh pr checks 29` (heads `599ee04`, `6005100`): 41 pass, 0 fail, 0 pending each.
- Pre-existing failures: none observed.

### Result

Both research tickets have their evidence on draft PRs that are not for merge. #28 holds the `Math.*` semantics table, Node vectors and Lean divergence examples. #29 holds the Dafny encoding measurements: isolated totals (verified/errors/timeouts) A 191/1/3, B 528/0/4, C 200/7/58; manual hints A 14, B 51, C 16; vector agreement B 100/0/0 and C 66/0/0; `-t js` builds fail for C_main and C_nan. Proof outcomes near the 30 s limit vary between runs, recorded in the REPORT. Follow-ups for the user: the `**` pass-through candidate issue and the `JSFloorDiv` precision limit above 2^53.
