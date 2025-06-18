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
  use U



lemma univ_is_OpenNeighb {X : Type} [TopologicalSpace X]
    (x : X) : OpenNeighbourhood Set.univ x := by
  constructor
  · trivial
  · exact isOpen_univ

lemma univ_is_Neighb {X : Type} [TopologicalSpace X]
    (x : X) : Neighbourhood Set.univ x := by
  apply OpenNeighb_is_Neighb
  constructor
  trivial
  exact isOpen_univ



-- basic set theory results


lemma left_empty_implies_disjoint_open_neighbourhoods
    {X : Type} {T : TopologicalSpace X} (C1 : Set X) (C2 : Set X) (hempty : C1 = ∅) : ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ Disjoint U1 U2 := by

  use ∅
  use Set.univ
  constructor
  exact isOpen_empty
  constructor
  exact isOpen_univ
  constructor
  exact Set.subset_empty_iff.mpr hempty
  constructor
  exact fun a _ ↦ trivial
  exact fun x a _ ↦ a


lemma right_empty_implies_disjoint_open_neighbourhoods
    {X : Type} {T : TopologicalSpace X} (C1 : Set X) (C2 : Set X) (hempty : C2 = ∅) : ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ Disjoint U1 U2 := by

  use Set.univ
  use ∅
  constructor
  exact isOpen_univ
  constructor
  exact isOpen_empty
  constructor
  exact fun a _ ↦ trivial
  constructor
  exact Set.subset_empty_iff.mpr hempty
  exact fun x _ a ↦ a
