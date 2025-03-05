import Mathlib.Tactic

-- ex 3
-- prove that the usual top. on ℝ is in fact a top

set_option linter.unusedVariables false

def Real.IsOpen (s : Set ℝ) : Prop :=
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s


lemma Real.isOpen_univ : IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 1
  constructor
  norm_num
  intro y hy
  trivial

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  specialize hs x hx.left
  specialize ht x hx.right
  cases' hs with δ1 hδ1
  cases' ht with δ2 hδ2
  use min δ1 δ2
  constructor
  · exact lt_min hδ1.left hδ2.left
  · intro y hy
    cases' hy with hy1 hy2
    constructor
    · apply hδ1.right
      have h1 : min δ1 δ2 ≤ δ1
      exact min_le_left δ1 δ2
      constructor
      <;> linarith
    · apply hδ2.right
      have h2 : min δ1 δ2 ≤ δ2
      exact min_le_right δ1 δ2
      constructor
      <;> linarith


lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  cases' hx with s hs

  have hs' : IsOpen s
  apply hF
  exact hs.left

  specialize hs' x hs.right
  cases' hs' with δ hδ
  cases' hδ with h1 h2
  use δ
  constructor
  · exact h1
  · intro y hy
    specialize h2 y hy
    simp
    use s
    constructor
    exact hs.left
    exact h2


def UsualTopology : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion

/-
Extra results needed:
-/

#check lt_min
#check min_le_left
#check min_le_right


/-
Lemma: open intervals (a, b) are open in ℝ with the usual topology
-/

lemma ioo_open_in_R (a b : ℝ) :
    UsualTopology.IsOpen ((Set.Ioo a b) : Set ℝ) := by

  rw [UsualTopology]
  intro x hx

  use min (x-a) (b-x)  -- nuestro δ

  constructor
  · -- δ > 0 ?
    simp
    exact hx

  · -- (x - δ, x + δ) ⊆ (a, b) ?

    -- hay que diferenciar cuando δ = x-a y δ = b-x

    have cases : (x - a < b - x) ∨ (x - a ≥ b - x)
    exact lt_or_le (x - a) (b - x)

    cases' cases with case1 case2

    · -- case δ = x-a
      intro y hy

      have hδ :  min (x-a) (b-x) = x-a
      simp
      linarith

      rw [hδ] at hy
      simp at hy
      simp
      constructor
      all_goals linarith

    · -- case δ = b-x
      intro y hy

      have hδ :  min (x-a) (b-x) = b-x
      simp
      linarith

      rw [hδ] at hy
      simp at hy
      simp
      constructor
      all_goals linarith
