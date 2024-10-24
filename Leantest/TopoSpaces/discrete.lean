import Mathlib.Tactic -- catarme los imports necesarios solo

-- import Mathlib.Topology.Basic
-- me falla classical em

-- ex 2
-- prove that the discrete top. space is in fact a top


/-
PROBLEMA: me gustaría separar esto en lemmas
pero me da problemas con los tipos...
-/


open TopologicalSpace

def DiscreteTopo (X : Type) : TopologicalSpace X where
  IsOpen (s : Set X) := s = Set.univ ∨ s = ∅
  isOpen_univ := by
    dsimp -- DEFINITIONAL SIMPLIFIER
    left
    rfl -- or trivial

  isOpen_inter := by
    dsimp
    intro s t hs ht

    cases' hs with hs hs
    cases' ht with ht ht

    · left -- 1. both are univ
      rw [hs, ht]
      simp
    · right -- 2. t is empty
      rw [ht]
      simp
    · right -- 3. s is empty
      rw [hs]
      simp

  isOpen_sUnion := by
    dsimp
    intro S hS

    have h : (Set.univ ∈ S) ∨ ¬ (Set.univ ∈ S)
    exact Classical.em (Set.univ ∈ S)

    cases' h with h h

    · left -- 1. ∃ t ∈ S with t = U
      ext s
      constructor <;> intro hs
      · trivial
      · simp
        use Set.univ

    · right
      simp
      intro s hs
      specialize hS s hs
      cases' hS with hS hS
      · by_contra
        rw [hS] at hs
        exact h hs
      · exact hS
