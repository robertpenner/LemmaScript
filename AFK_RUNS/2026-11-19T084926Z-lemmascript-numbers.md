# AFK Run: LemmaScript JavaScript number support, first chain (#14 parent, #15 to #18)

**Status:** completed

**Branch:** one worktree and branch per ticket, siblings of `LemmaScript/`; this log lives on `afk/numbers-1-log`, kept out of the ticket PRs.

**Pull request:** one fork PR per ticket: [#27](https://github.com/robertpenner/LemmaScript/pull/27) (#16), [#24](https://github.com/robertpenner/LemmaScript/pull/24) (#15), [#25](https://github.com/robertpenner/LemmaScript/pull/25) (#17), [#26](https://github.com/robertpenner/LemmaScript/pull/26) (#18).

**Started:** 2026-11-19 08:49:26 UTC

**Goal:** Land four independent, upstream-ready fixes from the #14 queue: `Number.isSafeInteger` on `real` operands (#16), `Math.min`/`Math.max` arity and typing (#15), `Math.trunc`/`Math.round` lowering (#17), and a hardened additions-only `.dfy` check (#18).

**Execution:** parallel, maximum 4 workers. Advisor and final reviewer: `gemini-4-carbon`.

**Verified integration head:** per-ticket PR heads `52af011` (#16), `b4be40d` (#15), `a163370` (#17), `72a781a` (#18), each based on `60cab87`.

### Slice progress

| Issue | Slice                               | Status              | Blocked by / reason | Integration commit | Verification                                     |
| ----- | ----------------------------------- | ------------------- | ------------------- | ------------------ | ------------------------------------------------ |
| #16   | `Number.isSafeInteger` on `real`    | integrated/verified |                     | `52af011` (PR #27) | 564 tests, 558 pass, 5 load timeouts rerun clean |
| #15   | `Math.min`/`Math.max` arity, typing | integrated/verified |                     | `b4be40d` (PR #24) | 564 tests, 563 pass, 0 fail, 1 skipped           |
| #17   | `Math.trunc`/`Math.round`           | integrated/verified |                     | `a163370` (PR #25) | 563 tests, 562 pass, 0 fail, 1 skipped           |
| #18   | additions-only check hardening      | integrated/verified |                     | `72a781a` (PR #26) | 589 tests, 588 pass, 0 fail, 1 skipped           |

### Parallel workers

| Ticket | Checkout            | Branch                               | Starting verified SHA | Allowed files                                                    | Worker state | Returned head | Integration commit |
| ------ | ------------------- | ------------------------------------ | --------------------- | ---------------------------------------------------------------- | ------------ | ------------- | ------------------ |
| #16    | `LemmaScript-ws-01` | `fix/is-safe-integer-real`           | `60cab87`             | resolve, transform, dafny-emit, lean-emit, new examples          | integrated   | `52af011`     | `52af011`          |
| #15    | `LemmaScript-ws-02` | `fix/math-min-max-arity`             | `60cab87`             | resolve, transform, extract, dafny-emit, lean-emit, new examples | integrated   | `b4be40d`     | `b4be40d`          |
| #17    | `LemmaScript-ws-03` | `feat/math-trunc-round`              | `60cab87`             | transform, dafny-emit, lean-emit, new examples, SPEC docs        | integrated   | `a163370`     | `a163370`          |
| #18    | `LemmaScript-ws-04` | `fix/check-additions-only-hardening` | `60cab87`             | dafny-commands (plus helper), new tools/tests                    | integrated   | `72a781a`     | `72a781a`          |

#15, #16, and #17 share `tools/src/transform.ts` and `tools/src/dafny-emit.ts`. Each PR is based on `60cab87`. An assembled merge of all four heads onto `60cab87` merges #15, #16, and #18 cleanly; #17 then conflicts in `SPEC_DAFNY.md`, `tools/src/dafny-emit.ts`, `tools/src/resolve.ts`, and `tools/tests/math-real.test.ts`. Whichever of #15, #16, and #17 merges later needs a rebase.

Briefs: [#16](https://github.com/robertpenner/LemmaScript/issues/16#issuecomment-7004467145), [#15](https://github.com/robertpenner/LemmaScript/issues/15#issuecomment-7004467426), [#17](https://github.com/robertpenner/LemmaScript/issues/17#issuecomment-7004467703), [#18](https://github.com/robertpenner/LemmaScript/issues/18#issuecomment-7004468038).

### Verification evidence

Baseline on clean `60cab87` (`npm run typecheck`, `npm run typecheck:examples`, `npm run build`, `./tools/test-fixtures.sh`): exit 0; node tests 562, pass 561, fail 0, skipped 1. No pre-existing failures.

Scope decision: #18 acceptance criteria 1 and 5 conflict (`examples/counter.dfy` and `examples/preorder.dfy` add clauses to generated method headers). This run implements only the `assume`/`{:axiom}` rejection, comment- and string-aware lexing, and rejection of added `lsc options` lines; header integrity is left for maintainer direction ([comment](https://github.com/robertpenner/LemmaScript/issues/18#issuecomment-7004817652)). The #18 PR uses `Refs #18`.

Per-ticket verification used `verify.sh`: `npm run typecheck`, `npm run typecheck:examples`, `npm run build`, `./regen-dafny.sh --no-verify` and `./regen-lean.sh` with a clean-diff check, then `./tools/test-fixtures.sh`.

- #16 on `52af011`: all steps exit 0 except fixtures, where 5 unit tests failed with `spawnSync ETIMEDOUT` / `System.TimeoutException` at high machine load (`batch-options`, `file-options`, `guard-command` x2, `indexed-access-types`). Those four files rerun alone: 60 of 60 pass. The script stops at the unit phase on failure, so the shell-fixture phase was run separately on `52af011`: exit 0.
- #15 on `b4be40d`: overall exit 0; 564 tests, 563 pass, 0 fail, 1 skipped.
- #17 on `a163370`: overall exit 0; 563 tests, 562 pass, 0 fail, 1 skipped. `tools/tests/math-real.test.ts`: 5 pass.
- #18 on `72a781a`: all steps exit 0 and the unit phase passed (589 tests, 588 pass, 0 fail, 1 skipped); the shell-fixture phase hit a Dafny timeout in `local-collections` at load average about 118. Rerun separately on `72a781a`: exit 0. `tools/tests/dafny-proof-additions.test.ts`: 27 pass; 4 of the new regression tests fail against `850eb37`. The check rejects none of the 81 committed `.dfy.gen` / `.dfy` pairs in `examples` and `casestudies`.

Pre-existing failures: none (baseline 0 fail). Every failure seen in this run was a load timeout in a file the ticket did not touch, and passed on rerun.

### Review

Each PR diff was reviewed by a `gemini-4-carbon` agent against its ticket brief; patches are pinned under the run scratch `review/` directory.

- #16: the false-fold for non-number types also covered types that may hold a number (`void`, numeric enums, branded numbers, interfaces `number` satisfies, discriminated unions), and folding discarded callee preconditions and division obligations in the argument. Fixed in `52af011`: those types are rejected and only a variable or literal argument folds.
- #15: an empty spread segment changed the result typing of `Math.min`/`Math.max` spreads. Fixed in `b4be40d`, with `SPEC.md` rows for the new forms. Lean has no `MathMin`/`MathMax` although `SPEC.md` lists them; recorded on [#15](https://github.com/robertpenner/LemmaScript/issues/15#issuecomment-7010352984) for maintainers.
- #17: `Math.trunc`/`Math.round` on a `nat` argument emitted `toNat` in Lean, and `mathTruncRound` was missing from the `lakefile` roots. Fixed in `a163370` with a failing-first test.
- #18: added lines containing `\r`, `\u2028`, or `\u2029`, identifiers starting with `?` or `'`, duplicates of a generated assume line, and comment or verbatim-string wrapping of a generated line could bypass the check. Fixed in `72a781a` with regression tests.

No actionable findings remain open. Maintainer decisions left open: header integrity for #18, `{:verify false}` on added declarations, Lean `MathMin`/`MathMax`, Lean `trunc`/`round` on reals, the existing `isSafeInteger` bigint path skipping `lowerExpr`, and `Math.floor`/`Math.ceil` on `nat` typed `int`.

### Recovery

Not resumed.

### Completion

PRs #24, #25, #26, and #27 marked ready for review. One `gh pr checks` poll per PR after CI finished: 41 of 41 checks pass on each final head (`b4be40d`, `a163370`, `72a781a`, `52af011`).

Final verification command: `verify.sh` per worktree (typecheck, typecheck:examples, build, regen diffs, `./tools/test-fixtures.sh`), with results listed under Verification evidence.

Elapsed duration: 4 h 37 min, from `Started:` to the `cee08d0` log commit at 2026-11-19T13:26:20Z.

**Result:** All four tickets (#15, #16, #17, #18) are implemented, reviewed, and verified on separate fork PRs, with hosted CI green. No upstream PRs were opened; that awaits the user's confirmation. #18 stays open for the header-integrity decision.
