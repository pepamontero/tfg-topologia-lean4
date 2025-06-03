import Leantest.Separation.def_H
import Leantest.MyDefs.my_inf

def F {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)

    : X → Set ℚ := fun x : X ↦ {p : ℚ | x ∈ H hT C1 C2 p}

lemma hF_non_empty {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    :  ∀ x : X, (F hT C1 C2 x).Nonempty := by
  intro x
  use 2
  simp [F, H]

lemma hFx_non_neg {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p : ℚ, p < 0 → p ∉ F hT C1 C2 x := by

  intro x p hp
  simp [F, H, hp]

lemma hFx_has_lb_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p, p ∈ F hT C1 C2 x → 0 ≤ p := by

  intro x p hp
  by_contra c
  simp at c
  apply hFx_non_neg hT C1 C2 x at c
  exact c hp

lemma hF_contains_bt1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p > 1, p ∈ F hT C1 C2 x := by

  intro x p hp
  have aux : ¬ p ≤ 0 := by linarith
  have aux' : ¬ (0 ≤ p ∧ p ≤ 1) := by by_contra; linarith
  simp [F, H, aux, aux', hp]
  linarith


-------- COMPORTAMIENTO DE F EN C1


lemma F_at_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

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

  · cases' Decidable.lt_or_eq_of_le hq with hq hq

    · apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 0 q hq
      apply set_inside_closure
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx

    · rw [← hq]
      exact H_C1_in_H0 hT C1 C2 hC1 hC2 hC1C2 hx


lemma F_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F hT C1 C2 x) 0 := by

  intro x hx
  constructor

  · intro y hy
    exact_mod_cast hFx_has_lb_0 hT C1 C2 x y hy

  · intro y hy
    rw [F_at_C1 hT C1 C2 hC1 hC2 hC1C2] at hy
    exact hy rfl
    exact hx


-- a partir de F quiero describir I que tome el infimo de F


def inclQR : ℚ → ℝ := fun q ↦ q

def F_Real {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : X → Set ℝ :=

    fun x ↦ inclQR '' (F hT C1 C2 x)


lemma relF_F_Real {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

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
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (F_Real hT C1 C2 x).Nonempty := by

  intro x
  simp [F_Real]
  exact hF_non_empty hT C1 C2 x

lemma F_Real_0_is_LB {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, 0 ∈ lowerBounds (F_Real hT C1 C2 x) := by

  intro x y hy
  simp [F_Real] at hy
  cases' hy with q hq
  cases' hq with hq hy
  simp [inclQR] at hy
  have aux : 0 ≤ q
  · exact hFx_has_lb_0 hT C1 C2 x q hq
  rw [← hy]
  exact Rat.cast_nonneg.mpr aux

lemma F_Real_BddBelow {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, BddBelow (F_Real hT C1 C2 x) := by

  intro x
  use 0
  exact F_Real_0_is_LB hT C1 C2 x


lemma F_Real_has_inf {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∃ r : ℝ, IsGLB (F_Real hT C1 C2 x) r := by

  intro x
  apply Real.exists_isGLB
  exact F_Real_Nonempty hT C1 C2 x
  exact F_Real_BddBelow hT C1 C2 x

lemma F_Real_1inf {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, ∀ p : ℚ, p > 1 → inclQR p ∈ F_Real hT C1 C2 x := by
  intro x p hp
  simp [F_Real]
  use (p : ℚ)
  constructor
  · exact hF_contains_bt1 hT C1 C2 x p hp
  · rfl


lemma F_Real_0_GLB_in_C1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → IsGLB (F_Real hT C1 C2 x) 0 := by

  intro x hx
  rw [relF_F_Real]
  have aux := F_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx
  obtain ⟨h1, _⟩ := aux

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
