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

def TrivialTopology (X : Type) : TopologicalSpace X where
  IsOpen (s : Set X) := s = Set.univ ∨ s = ∅
  isOpen_univ := by
    left
    rfl

  isOpen_inter := by
    intro s t hs ht
    cases' hs with hs_univ hs_empty
    cases' ht with ht_univ ht_empty

    · left -- 1. both are univ
      rw [hs_univ, ht_univ]
      simp
    · right -- 2. t is empty
      rw [ht_empty]
      simp
    · right -- 3. s is empty
      rw [hs_empty]
      simp

  isOpen_sUnion := by
    intro S hS

    cases' Classical.em (Set.univ ∈ S) with h1 h2
    -- h1 : Set.univ ∈ S
    -- h2 : Set.univ ∉ S

    · left
      ext s
      constructor <;> intro hs
      · trivial
      · use Set.univ -- uses h1 implicitly to close the goal

    · right
      simp
      intro s hs
      specialize hS s hs
      cases' hS with hS hS
      · by_contra
        rw [hS] at hs
        exact h2 hs
      · exact hS
