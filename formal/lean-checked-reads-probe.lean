/-
  Minimal Lean 4 probe for midspiral/LemmaScript#387 (robertpenner/LemmaScript#44):
  Contrasts PR #379's Lean lowering against a clean checked-reads lowering for
  pure functions vs. imperative/monadic methods.

  Verified standalone with: `lean formal/lean-checked-reads-probe.lean`
-/

namespace CheckedReadsProbe

structure Leaf where
  value : Int

structure Middle where
  leaf : Option Leaf

structure Tree where
  middle : Option Middle

/-- Checked read helper (mirrors `LemmaScript.optionValue` from PR #379). -/
def optionValue {α : Type} (x : Option α) : Option α := x

-- =========================================================================
-- 1. PR #379 pattern: pure functions forced into monadic `Option` / Velvet
--    because checked reads call `optionValue` in `do` notation.
--    Consequence: `Pure.deepAccess` cannot be emitted as a pure `Tree -> Int`
--    function; callers/proofs lose pure unfolding and must use method specs.
-- =========================================================================

def deepAccess_monadic (t : Tree) : Option Int := do
  let mut branch0 : Bool := t.middle.isSome
  if branch0 then
    let m ← optionValue t.middle
    branch0 := m.leaf.isSome
  if branch0 then
    let m ← optionValue t.middle
    let l ← optionValue m.leaf
    return l.value
  return 0

-- Notice: `deepAccess_monadic` returns `Option Int`, not `Int`, so pure spec
-- callers cannot write `deepAccess_monadic t = 0` without unwrapping `some`.

-- =========================================================================
-- 2. Clean pure lowering for immutable/pure TS functions:
--    Keep a genuine Lean proof obligation (`Option.get` with dependent `if h :`)
--    while remaining a total pure `def : Tree -> Int` (no default erasure, no
--    monad wrapper, no `let _compareN` temporaries for pure comparisons).
-- =========================================================================

def Pure_deepAccess (t : Tree) : Int :=
  if h1 : t.middle.isSome then
    let m := t.middle.get h1
    if h2 : m.leaf.isSome then
      (m.leaf.get h2).value
    else
      0
  else
    0

-- Pure comparison without `let _compareN` churn:
-- `res.truncatedBy === "bytes"` lowers directly to `res == some "bytes"`.
def Pure_isBytes (truncatedBy : Option String) : Bool :=
  truncatedBy == some "bytes"

-- =========================================================================
-- 3. Proofs stay short and automatic with `simp` / `cases` (no tactic macros,
--    no `by grind` inside dependent `ensures` if statements).
-- =========================================================================

theorem deepAccess_none (t : Tree) (h : t.middle = none) :
    Pure_deepAccess t = 0 := by
  simp [Pure_deepAccess, h]

theorem deepAccess_some (t : Tree) (m : Middle) (l : Leaf)
    (hm : t.middle = some m) (hl : m.leaf = some l) :
    Pure_deepAccess t = l.value := by
  simp [Pure_deepAccess, hm, hl]

theorem deepAccess_monadic_agrees (t : Tree) :
    deepAccess_monadic t = some (Pure_deepAccess t) := by
  cases hm : t.middle with
  | none =>
    simp [deepAccess_monadic, Pure_deepAccess, hm]
  | some m =>
    cases hl : m.leaf with
    | none =>
      simp [deepAccess_monadic, Pure_deepAccess, optionValue, hm, hl]
    | some l =>
      simp [deepAccess_monadic, Pure_deepAccess, optionValue, hm, hl]

theorem isBytes_iff (s : Option String) :
    Pure_isBytes s = true ↔ s = some "bytes" := by
  simp [Pure_isBytes]

-- =========================================================================
-- 4. Soundness check: an unguarded checked read in a pure function DOES NOT
--    elaborate (cannot silently erase the check or synthesize a default):
--    `def bad (x : Option Int) : Int := x.get (by assumption)` fails to typecheck.
-- =========================================================================

/--
error: Tactic `assumption` failed

x : Option Int
⊢ x.isSome = true
-/
#guard_msgs in
def bad_unguarded_read (x : Option Int) : Int :=
  x.get (by assumption)

end CheckedReadsProbe
