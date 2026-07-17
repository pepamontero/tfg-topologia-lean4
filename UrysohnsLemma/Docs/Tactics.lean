-- ANCHOR: import_mathlib_tactic
import Mathlib.Tactic
-- ANCHOR_END: import_mathlib_tactic

/-
Real, compiling Lean source backing the code samples in the "Demostraciones en Lean"
part of the "Lean Theorem Prover" chapter (`Docs/LeanProver.lean`), covering tactic
mode and the basic tactics (`intro`, `exact`, `apply`, `use`, `left`/`right`,
`constructor`, `cases'`).

Every snippet here uses `example`, which binds no name, so no `section`/`namespace`
isolation is strictly required for name collisions; sections are used purely to group
related examples by subsection. Many snippets are intentionally incomplete in the
manual (to display a particular mid-proof goal state via hover). To keep this file
itself free of errors (a real error anywhere in a file would break extraction of every
anchor in it), such snippets are closed with a `sorry` placed *after* the
`-- ANCHOR_END:` marker, so it is not part of the text shown in the manual, but still
makes the surrounding declaration compile.

Two examples below (`apply`/`left` sections) fix what appears to be a typo in the
original prose (`example : (p q : Prop) ...` is not valid Lean; the colon right after
`example` must be dropped, as it is everywhere else in the chapter).
-/

section ByExamplePQ
-- ANCHOR: by_pq_and
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
-- ANCHOR_END: by_pq_and
  sorry
end ByExamplePQ

section IntroTactic
-- ANCHOR: intro_before1
example (p : Prop) : p → p := by
-- ANCHOR_END: intro_before1
  sorry

-- ANCHOR: intro_after1
example (p : Prop) : p → p := by
  intro hp
-- ANCHOR_END: intro_after1
  sorry

-- ANCHOR: intro_before2
example : ∀ (p : Prop), p → p := by
-- ANCHOR_END: intro_before2
  sorry

-- ANCHOR: intro_after2
example : ∀ (p : Prop), p → p := by
  intro q
-- ANCHOR_END: intro_after2
  sorry
end IntroTactic

section ExactTactic
-- ANCHOR: exact_before1
example : ∀ (p : Prop), p → p := by
  intro p hp
-- ANCHOR_END: exact_before1
  sorry

-- ANCHOR: exact_after1
example : ∀ (p : Prop), p → p := by
  intro p hp
  exact hp
-- ANCHOR_END: exact_after1

-- ANCHOR: exact_term_mode
example : ∀ (p : Prop), p → p := fun p ↦ (fun hp : p ↦ hp)
-- ANCHOR_END: exact_term_mode
end ExactTactic

section ApplyTactic
-- ANCHOR: apply_before
example (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
-- ANCHOR_END: apply_before
  sorry

-- ANCHOR: apply_after
example (p q : Prop) (hp : p)
    (hpq : p → q) : q := by
  apply hpq
-- ANCHOR_END: apply_after
  sorry
end ApplyTactic

section UseTactic
-- ANCHOR: use_before
example : ∃ n : ℕ, n > 3 := by
-- ANCHOR_END: use_before
  sorry

-- ANCHOR: use_after
example : ∃ n : ℕ, n > 3 := by
  use 5
-- ANCHOR_END: use_after
  sorry
end UseTactic

section LeftRightTactic
-- ANCHOR: leftright_before
example (p q : Prop) (hp : p) :
    p ∨ q := by
-- ANCHOR_END: leftright_before
  sorry

-- ANCHOR: leftright_after
example (p q : Prop) (hp : p) :
    p ∨ q := by
  left
-- ANCHOR_END: leftright_after
  sorry
end LeftRightTactic

section ConstructorTactic
-- ANCHOR: constructor_before
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
-- ANCHOR_END: constructor_before
  sorry

-- ANCHOR: constructor_after
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
-- ANCHOR_END: constructor_after
  sorry
  sorry

-- ANCHOR: constructor_complete
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq
-- ANCHOR_END: constructor_complete

-- ANCHOR: constructor_dot_before
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  ·
-- ANCHOR_END: constructor_dot_before
    sorry
  sorry

-- ANCHOR: constructor_dot_complete
example (p q : Prop) (hp : p)
    (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq
-- ANCHOR_END: constructor_dot_complete
end ConstructorTactic

section CasesTactic
-- ANCHOR: cases_before
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
-- ANCHOR_END: cases_before
  sorry

-- ANCHOR: cases_after
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
-- ANCHOR_END: cases_after
  sorry
  sorry

-- ANCHOR: cases_complete
example (p q : Prop) (h : p ∨ q)
    (hpq : p → q) : q := by
  cases' h with hp hq
  · apply hpq
    exact hp
  · exact hq
-- ANCHOR_END: cases_complete
end CasesTactic
