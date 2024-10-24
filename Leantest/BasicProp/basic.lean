import Mathlib.Tactic

/-
Demostrar los siguientes resultados:

-/

#check isOpen_empty
example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  have h1 : ∅ = ⋃₀ ∅
  simp
  rw [h1]
  apply isOpen_sUnion
  intro t ht
  by_contra
  exact ht
