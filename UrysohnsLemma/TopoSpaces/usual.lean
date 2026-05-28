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
  obtain ⟨δ1, hδ1, hs⟩ := hs x hx.left
  obtain ⟨δ2, hδ2, ht⟩ := ht x hx.right
  use min δ1 δ2
  constructor
  · exact lt_min hδ1 hδ2
  · intro y hy
    constructor
    · apply hs
      have hδ := min_le_left δ1 δ2
      constructor
      all_goals linarith
    · apply ht
      have hδ := min_le_right δ1 δ2
      constructor
      all_goals linarith


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
    simp only [lt_inf_iff]
    exact ⟨sub_pos.mpr hx.1, sub_pos.mpr hx.2⟩

  · -- (x - δ, x + δ) ⊆ (a, b) ?
    -- hay que diferenciar cuando δ = x-a y δ = b-x
    intro y hy
    have cases := lt_or_ge (x - a) (b - x)
    cases' cases with h h
    all_goals
      try rw [min_eq_left_of_lt h] at hy
      try rw [min_eq_right h] at hy
      simp at hy
      constructor
      all_goals linarith

/--
Proof that my Usual Topology is equivalent to the one Mathlib tipically uses.
-/
lemma mathlib_open_eq_my_open : @UniformSpace.toTopologicalSpace ℝ (by exact PseudoEMetricSpace.toUniformSpace) = UsualTopology := by
  apply TopologicalSpace.ext
  apply funext
  intro s
  rw [isOpen_iff_nhds]
  simp
  constructor
  · intro hs x hx
    obtain ⟨δ, ⟨hδ0, hδ⟩⟩ := Metric.mem_nhds_iff.mp (hs x hx)
    refine ⟨δ, hδ0, ?_⟩
    intro y hy
    apply hδ
    simp [Real.dist_eq, abs_lt]
    exact ⟨lt_add_of_tsub_lt_left hy.1, sub_left_lt_of_lt_add hy.2⟩
  · intro hs x hx
    rw [Metric.mem_nhds_iff]
    obtain ⟨δ, ⟨hδ0, hδ⟩⟩ := hs x hx
    refine ⟨δ, hδ0, ?_⟩
    intro y hy
    apply hδ y
    simp [Real.dist_eq] at hy
    exact ⟨sub_lt_of_abs_sub_lt_left hy,
      lt_add_of_tsub_lt_left (abs_lt.mp hy).2⟩
