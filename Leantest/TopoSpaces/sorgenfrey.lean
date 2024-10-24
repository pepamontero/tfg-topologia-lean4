import Mathlib.Tactic

-- ex 4
-- prove that the sorgenfrey top. on ℝ is in fact a top

set_option linter.unusedVariables false

def Sorgenfrey.IsOpen (s : Set ℝ) :=  ∀ x ∈ s, ∃ δ > 0, Set.Ico x (x + δ) ⊆ s

lemma Sorgenfrey.isOpen_univ : IsOpen (Set.univ : Set ℝ) := by
  intros x hx -- podemos hacer intro porque hay ∀ en la definición
  use 1
  apply And.intro
  · norm_num -- 1 > 0
  · intro y hy -- [x, x+1) ⊆ Univ
    trivial

lemma Sorgenfrey.isOpen_inter (A B : Set ℝ) (hA : IsOpen A) (hB : IsOpen B) : IsOpen (A ∩ B) := by
  intro x hx
  rw [Set.mem_inter_iff] at hx
  specialize hA x hx.left
  specialize hB x hx.right
  cases' hA with δ1 h1
  cases' hB with δ2 h2
  use min δ1 δ2
  apply And.intro

  -- min δ1 δ2 > 0
  · exact lt_min h1.left h2.left

  -- [x, x + min δ1 δ2) ⊆ A ∩ B
  · intros y hy
    rw [Set.mem_inter_iff]
    apply And.intro
    -- y ∈ A
    · cases' h1 with h1 h1'
      apply h1'
      rw [Set.mem_Ico] at *
      apply And.intro
      exact hy.left
      have aux : x + min δ1 δ2 ≤ x + δ1
      simp
      linarith

    -- y ∈ B
    · cases' h2 with h2 h2'
      apply h2'
      rw [Set.mem_Ico] at *
      apply And.intro
      exact hy.left
      have aux : x + min δ1 δ2 ≤ x + δ2
      simp
      linarith

lemma Sorgenfrey.isOpen_sUnion (S : Set (Set ℝ)) (hS : ∀ t ∈ S, IsOpen t) : IsOpen (⋃₀ S) := by
  intro x hx
  cases' hx with t ht
  specialize hS t ht.left x ht.right
  cases' hS with δ hδ
  use δ
  apply And.intro
  -- δ > 0
  · exact hδ.left
  -- [x, x + δ) ⊆ ⋃₀ S
  · trans t
    exact hδ.right
    intro y hy
    exact Set.mem_sUnion_of_mem hy ht.left


def Sorgenfrey : TopologicalSpace ℝ where
  IsOpen (s : Set ℝ) :=  ∀ x ∈ s, ∃ δ > 0, Set.Ico x (x + δ) ⊆ s
  isOpen_univ := Sorgenfrey.isOpen_univ
  isOpen_inter := Sorgenfrey.isOpen_inter
  isOpen_sUnion := Sorgenfrey.isOpen_sUnion


/-
Results used
-/

--Add.intro
#check lt_min
#check Set.mem_inter_iff
#check Set.mem_Ico
#check Set.mem_sUnion_of_mem
