import UrysohnsLemma.BasicProp.open


-- DEFINICIÓN DE INTERIOR DE UN CONJUNTO
#check interior
def Interior {X : Type} [TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∃ U : Set X, OpenNeighbourhood U x ∧ U ⊆ A}


#check isOpen_interior
-- EL INTERIOR DE UN CONJUNTO ES UN ABIERTO
-- ANCHOR: isOpen_interior_example
example {X : Type} [T : TopologicalSpace X]
    (A : Set X) : IsOpen (interior A) := by
  apply A_open_iff_neighbourhood_of_all.mpr
  intro a ha
  obtain ⟨U, hU, ha⟩ := ha
  use U
  constructor
  · intro x hx
    use U
  · constructor
    · exact ha
    · exact hU.left
-- ANCHOR_END: isOpen_interior_example

#check interior_subset
-- ANCHOR: interior_subset_example
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    interior A ⊆ A := by
  intro a ha
  obtain ⟨U, hU, ha⟩ := ha
  apply hU.right
  exact ha
-- ANCHOR_END: interior_subset_example

#check interior_eq_iff_isOpen
-- ANCHOR: interior_eq_iff_isOpen_forward
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen A ↔ interior A = A:= by
  constructor; swap; all_goals intro h
  · rw [← h]
    exact isOpen_interior
-- ANCHOR_END: interior_eq_iff_isOpen_forward
-- ANCHOR: interior_eq_iff_isOpen_backward
  · apply Set.Subset.antisymm
    · exact interior_subset
    · intro a ha
      use A
      constructor
      · simp
        exact h
      · exact ha
-- ANCHOR_END: interior_eq_iff_isOpen_backward
