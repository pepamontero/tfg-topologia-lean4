import Mathlib.Tactic

/-
Real, compiling Lean source backing the code samples in the "Herramientas de
automatización y búsqueda en Mathlib" and "Noncomputable y el axioma de elección"
parts of the "Lean Theorem Prover" chapter (`Docs/LeanProver.lean`).

As in `Tactics.lean`, incomplete snippets are closed with a `sorry` placed after the
`-- ANCHOR_END:` marker so the file compiles without errors while the manual only
displays the text between the markers. One example from the manual (the very first
`exact?` failing to close `x / x = 1`) is intentionally *not* reproduced here: `exact?`
failing is a hard elaboration error in Lean (unlike an incomplete/`sorry`-able proof,
it cannot be neutralized by adding more tactics afterwards), and since anchor
extraction builds the whole module, a single such error would break every other real
anchor in the file. That one snippet is kept as plain static text in the manual.

`indefinite Description` lives under the `Classical` namespace; `open Classical in`
(placed outside the anchors) lets the displayed code keep using the bare name exactly
as in the manual's prose.
-/

section SimpTactic
-- ANCHOR: simp_group
example (G : Type) [Group G] (a b c : G) :
    a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp
-- ANCHOR_END: simp_group
end SimpTactic

section ExactQExamples
-- ANCHOR: exactq_local
example (p : Prop) : p → p := by
  intro hp
  exact?
-- ANCHOR_END: exactq_local

-- ANCHOR: exactq_mathlib
example (n : ℕ) : n ≥ 0 := by
  exact?
-- ANCHOR_END: exactq_mathlib
end ExactQExamples

section HaveExamples
-- ANCHOR: have_goal_r_stmt
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r
-- ANCHOR_END: have_goal_r_stmt
  := sorry

-- ANCHOR: have_goal_r_incomplete
example (p q r : Prop) (hpq : p → q)
    (hqr : q → r) (hp : p) : r := by
  have hq : q
-- ANCHOR_END: have_goal_r_incomplete
  sorry
  sorry

-- ANCHOR: have_goal_r_complete
example (p q r : Prop) (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q
  · apply hpq
    exact hp
  apply hqr
  exact hq
-- ANCHOR_END: have_goal_r_complete
end HaveExamples

section XDivXExamples
-- ANCHOR: xdivx_have_empty
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  have h : x ≠ 0
  ·
-- ANCHOR_END: xdivx_have_empty
    sorry
  sorry

-- ANCHOR: xdivx_have_exactq
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  have h : x ≠ 0
  · exact?
-- ANCHOR_END: xdivx_have_exactq
  sorry

-- ANCHOR: xdivx_complete
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  have h : x ≠ 0
  · exact Ne.symm (ne_of_lt hx)
  exact?
-- ANCHOR_END: xdivx_complete

-- ANCHOR: xdivx_apply_divself
example (x : ℝ) (hx : x > 0) :
    x / x = 1 := by
  apply div_self
-- ANCHOR_END: xdivx_apply_divself
  sorry
end XDivXExamples

namespace ChoiceExample
open Classical in
-- ANCHOR: choice_axiom
axiom choice {α : Sort u} : Nonempty α → α
-- ANCHOR_END: choice_axiom

open Classical in
-- ANCHOR: choose_def
noncomputable def choose {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val
-- ANCHOR_END: choose_def

open Classical in
-- ANCHOR: choose_spec_def
theorem choose_spec {α : Sort u} {p : α → Prop}
    (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property
-- ANCHOR_END: choose_spec_def
end ChoiceExample
