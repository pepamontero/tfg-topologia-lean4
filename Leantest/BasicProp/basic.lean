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

open TopologicalSpace



def OpenNeighbourhood {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : Prop :=
    x ∈ U ∧ IsOpen U

def Neighbourhood {X : Type} [TopologicalSpace X]
    (V : Set X) (x : X) : Prop :=
    ∃ U : Set X, U ⊆ V ∧ OpenNeighbourhood U x

lemma OpenNeighb_is_Neighb {X : Type} [TopologicalSpace X]
    (U : Set X) (x : X) : OpenNeighbourhood U x →
    Neighbourhood U x := by
  intro hU
  rw [Neighbourhood]
  use U



lemma univ_is_OpenNeighb {X : Type} [TopologicalSpace X]
    (x : X) : OpenNeighbourhood Set.univ x := by
  constructor
  trivial
  exact isOpen_univ

lemma univ_is_Neighb {X : Type} [TopologicalSpace X]
    (x : X) : Neighbourhood Set.univ x := by
  apply OpenNeighb_is_Neighb
  constructor
  trivial
  exact isOpen_univ
