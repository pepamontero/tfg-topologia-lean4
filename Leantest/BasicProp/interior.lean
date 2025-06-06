import Mathlib.Tactic
import Leantest.BasicProp.basic
import Leantest.BasicProp.open


-- DEFINICIÓN DE INTERIOR DE UN CONJUNTO
#check interior
def Interior {X : Type} [T : TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∃ U : Set X, OpenNeighbourhood U x ∧ U ⊆ A}


#check isOpen_interior
-- EL INTERIOR DE UN CONJUNTO ES UN ABIERTO
lemma interior_is_open {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen (Interior A) := by

  refine (characterization_of_open (Interior A)).mpr ?_
  intro x hx
  rw [Interior] at hx
  simp at hx
  cases' hx with U hU
  use U
  constructor
  · exact hU.left
  · intro y hy
    rw [Interior]
    simp
    use U
    constructor
    · constructor
      · exact hy
      · exact hU.left.right
    · exact hU.right
