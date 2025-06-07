import Leantest.BasicProp.open


-- DEFINICIÓN DE INTERIOR DE UN CONJUNTO
#check interior
def Interior {X : Type} [T : TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∃ U : Set X, OpenNeighbourhood U x ∧ U ⊆ A}


#check isOpen_interior
-- EL INTERIOR DE UN CONJUNTO ES UN ABIERTO
lemma interior_is_open {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen (Interior A) := by

  apply A_open_iff_neighbourhood_of_all.mpr
  simp [Neighbourhood]

  intro x hx
  rw [Interior] at hx
  simp at hx
  cases' hx with U hU
  use U
  constructor
  · intro y hy
    rw [Interior]
    simp
    use U
    constructor
    · constructor
      · exact hy
      · exact hU.left.right
    · exact hU.right
  · exact hU.left

#check interior_subset
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    interior A ⊆ A := by
  intro a ha
  obtain ⟨U, hU⟩ := ha
  apply hU.left.right
  exact hU.right

#check interior_eq_iff_isOpen
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen A ↔ interior A = A:= by

  constructor
  all_goals intro h
  · apply Set.Subset.antisymm
    · exact interior_subset
    · intro a ha
      use A
      constructor
      · simp
        exact h
      · exact ha

  · rw [← h]
    exact isOpen_interior
