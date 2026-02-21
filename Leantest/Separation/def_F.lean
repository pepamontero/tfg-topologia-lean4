import Leantest.Separation.def_H
import Leantest.MyDefs.my_inf

def F {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : X → Set ℚ := fun x : X ↦ {p : ℚ | x ∈ H hT C1 C2 p}

lemma hF_non_empty {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    :  ∀ x : X, (F hT C1 C2 x).Nonempty := by
  intro x
  use 2
  simp [F, H]
  norm_num

lemma hFx_non_neg {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p : ℚ, p < 0 → p ∉ F hT C1 C2 x := by

  intro x p hp
  simp [F, H, hp]

lemma hFx_has_lb_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, 0 ∈ lowerBounds (F hT C1 C2 x) := by

  intro x p hp
  by_contra c
  simp at c
  apply hFx_non_neg hT C1 C2 x at c
  exact c hp

lemma hF_contains_bt1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p > 1, p ∈ F hT C1 C2 x := by

  intro x p hp
  have aux : ¬ p ≤ 0 := by linarith
  have aux' : ¬ (0 ≤ p ∧ p ≤ 1) := by by_contra; linarith
  simp [F, H, aux']
  linarith

-------- COMPORTAMIENTO DE F EN C1


lemma F_at_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → F hT C1 C2 x = {q : ℚ | q ≥ 0} := by

  intro x hx
  ext q
  constructor
  all_goals intro hq

  · by_contra c
    simp at c
    apply hFx_non_neg hT C1 C2 x at c
    exact c hq

  · simp only [ge_iff_le, Set.mem_setOf_eq] at hq
    cases' Decidable.lt_or_eq_of_le hq with hq hq

    · apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 0 q hq
      apply subset_closure
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx

    · rw [← hq]
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx

lemma F_at_C2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C2 → F hT C1 C2 x = {q : ℚ | q > 1} := by

  intro x hx
  ext q
  constructor
  all_goals intro hq

  · by_contra c
    simp at c

    have aux : x ∈ (H hT C1 C2 1)
    · cases' (Decidable.lt_or_eq_of_le c) with c c
      · apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 q 1 c
        apply subset_closure
        exact hq
      · rw [c] at hq
        exact hq

    rw [H_value1 hT C1 C2] at aux
    exact aux hx

  · simp at hq
    simp [F]
    rw [H_at_bt1_is_univ hT C1 C2]
    trivial
    exact hq

lemma F_1_LB_in_C2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C2 → 1 ∈ lowerBounds (F hT C1 C2 x) := by

  intro x hx q hq

  by_contra c
  simp at c

  rw [← Set.notMem_compl_iff, ← H_value1 hT C1 C2] at hx
  have aux : H hT C1 C2 q ⊆ H hT C1 C2 1
  · trans closure (H hT C1 C2 q)
    · exact subset_closure
    · exact H_isOrdered hT C1 C2 hC1 hC2 hC1C2 q 1 c
  apply aux at hq
  exact hx hq


lemma F_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F hT C1 C2 x) 0 := by

  intro x hx
  constructor

  · intro y hy
    exact_mod_cast hFx_has_lb_0 hT C1 C2 x hy

  · intro y hy
    rw [F_at_C1 hT C1 C2 hC1 hC2 hC1C2] at hy
    exact hy rfl
    exact hx

lemma F_1_GLB_in_C2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C2 → IsGLB (F hT C1 C2 x) 1 := by

  intro x hx

  constructor
  · exact F_1_LB_in_C2 hT C1 C2 hC1 hC2 hC1C2 x hx

  · intro q hq
    simp [lowerBounds] at hq

    by_contra hc
    simp at hc

    have hp : ∃ p : ℚ, 1 < p ∧ p < q
    · exact_mod_cast exists_rat_btwn hc

    obtain ⟨p, hp1, hpq⟩ := hp

    have hp' : p ∈ F hT C1 C2 x
    · rw [F_at_C2 hT C1 C2 hC1 hC2 hC1C2 x hx]
      exact hp1
    specialize hq hp'
    linarith


-- a partir de F quiero describir I que tome el infimo de F


def inclQR : ℚ → ℝ := fun q ↦ q

def F_Real {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → Set ℝ :=

    fun x ↦ inclQR '' (F hT C1 C2 x)


lemma relF_F_Real {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : ∀ x : X,
    F_Real hT C1 C2 x = {q : ℝ | ∃ p : ℚ, q = p ∧ p ∈ F hT C1 C2 x}
    := by

  intro x
  ext r
  constructor
  all_goals intro hr

  · simp
    rw [F_Real] at hr
    obtain ⟨p, hp⟩ := hr
    use p
    constructor
    · rw [inclQR] at hp
      exact Eq.symm hp.right
    · exact hp.left

  · simp at hr
    rw [F_Real]
    obtain ⟨p, hp⟩ := hr
    use p
    constructor
    · exact hp.right
    · rw [inclQR]
      exact Eq.symm hp.left


------ GLB

lemma F_Real_Nonempty {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (F_Real hT C1 C2 x).Nonempty := by

  intro x
  simp [F_Real]
  exact hF_non_empty hT C1 C2 x

lemma F_Real_0_is_LB {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, 0 ∈ lowerBounds (F_Real hT C1 C2 x) := by

  intro x y hy
  simp [F_Real] at hy
  cases' hy with q hq
  cases' hq with hq hy
  simp [inclQR] at hy
  have aux : 0 ≤ q
  · exact hFx_has_lb_0 hT C1 C2 x hq
  rw [← hy]
  exact Rat.cast_nonneg.mpr aux

lemma F_Real_BddBelow {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, BddBelow (F_Real hT C1 C2 x) := by

  intro x
  use 0
  exact F_Real_0_is_LB hT C1 C2 x


lemma F_Real_has_inf {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∃ r : ℝ, IsGLB (F_Real hT C1 C2 x) r := by

  intro x
  apply Real.exists_isGLB
  exact F_Real_Nonempty hT C1 C2 x
  exact F_Real_BddBelow hT C1 C2 x

lemma F_Real_1inf {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p : ℚ, p > 1 → inclQR p ∈ F_Real hT C1 C2 x := by
  intro x p hp
  simp [F_Real]
  use (p : ℚ)
  constructor
  · exact hF_contains_bt1 hT C1 C2 x p hp
  · rfl


lemma F_Real_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F_Real hT C1 C2 x) 0 := by

  intro x hx
  rw [relF_F_Real]
  obtain ⟨h1, _⟩ := F_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx

  constructor
  · intro r hr
    obtain ⟨p, hp1, hp2⟩ := hr
    specialize h1 hp2
    rw [hp1]
    exact_mod_cast h1

  · intro r hr
    simp [lowerBounds] at hr
    specialize @hr (0 : ℝ) (0 : ℚ) (by exact Eq.symm Rat.cast_zero)
    apply hr
    rw [F_at_C1 hT C1 C2 hC1 hC2 hC1C2]
    simp
    exact hx

example (a b : ℝ) (h : a < b) : ¬ a ≥ b := by exact not_le_of_lt h

lemma F_Real_1_GLB_in_C2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C2 → IsGLB (F_Real hT C1 C2 x) 1 := by

  intro x hx
  rw [relF_F_Real]
  obtain ⟨h1, _⟩ := F_1_GLB_in_C2 hT C1 C2 hC1 hC2 hC1C2 x hx

  constructor
  · intro r hr
    obtain ⟨p, hp1, hp2⟩ := hr
    specialize h1 hp2
    rw [hp1]
    exact_mod_cast h1

  · intro r hr
    have aux : ∀ p ∈ F hT C1 C2 x, r ≤ p
    · intro p hp
      simp [lowerBounds] at hr
      specialize @hr (inclQR p) p rfl hp
      exact hr

    by_contra c
    simp at c
    have aux'' : ∃ p : ℚ, 1 < p ∧ p < r
    · exact_mod_cast exists_rat_btwn c
    obtain ⟨p, hp1, hpr⟩ := aux''
    have hp : p ∈ F hT C1 C2 x
    · exact hF_contains_bt1 hT C1 C2 x p hp1
    specialize aux p hp
    apply not_le_of_lt at hpr
    exact hpr aux
