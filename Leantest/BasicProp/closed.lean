import Mathlib.Tactic

/-
Note that:
class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
-/

#check Set.compl_univ
example {X : Type} : (Set.univ : Set X)ᶜ = ∅ := by
  -- exact compl_univ
  ext x
  constructor <;> intro h
  · simp at h
  · simp
    trivial

#check Set.compl_empty
example {X : Type} : (∅ : Set X)ᶜ = Set.univ := by
  rw [← compl_compl Set.univ]
  rw [compl_inj_iff]
  exact Eq.symm Set.compl_univ


#check isClosed_univ
example (X : Type) [TopologicalSpace X] : IsClosed (Set.univ : Set X) := by
  rw [← isOpen_compl_iff]
  rw [Set.compl_univ]
  exact isOpen_empty

#check isClosed_empty
example (X : Type) [TopologicalSpace X] : IsClosed (∅ : Set X) := by
  rw [← isOpen_compl_iff]
  rw [Set.compl_empty]
  exact isOpen_univ

#check IsClosed.union
example (X : Type) [TopologicalSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) : IsClosed (A ∪ B) := by
  rw [← isOpen_compl_iff] at *
  rw [Set.compl_union]
  apply TopologicalSpace.isOpen_inter
  exact hA
  exact hB

#check isClosed_sInter
example (X : Type) [TopologicalSpace X] (S : Set (Set X)) (hS : ∀ t ∈ S, IsClosed t) : IsClosed (⋂₀ S) := by
  rw [← isOpen_compl_iff]
  rw [Set.compl_sInter]
  apply TopologicalSpace.isOpen_sUnion
  intro t ht
  simp at ht
  cases' ht with s hs
  specialize hS s hs.left
  rw [← isOpen_compl_iff] at hS
  rw [hs.right] at hS
  exact hS
