import Mathlib.Tactic


/-
Basic results on sets that i haven't found
in mathlib
-/

lemma nonempty_has_element {X : Type} (A : Set X)
    (hA : A ≠ ∅) : ∃ x : X, x ∈ A := by
  by_contra hc

  have aux : A = ∅
  · ext x
    constructor
    · intro hx
      apply hc
      use x
    · intro hx
      by_contra
      exact hx

  exact hA aux
