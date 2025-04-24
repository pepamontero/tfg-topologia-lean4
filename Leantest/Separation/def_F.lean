import Leantest.Separation.def_H


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


-- a partir de F quiero describir I que tome el infimo de F


def inclQR : ℚ → ℝ := fun q ↦ q

def F_Real {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : X → Set ℝ :=

    fun x ↦ inclQR '' (F hT C1 C2 x)

#check Real.exists_isGLB

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


noncomputable def k {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ℝ :=
    fun x ↦ Classical.choose (F_Real_has_inf hT C1 C2 x)

lemma k_prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x, IsGLB (F_Real hT C1 C2 x) (k hT C1 C2 x) := by

  intro x
  rw [k]
  exact Classical.choose_spec (F_Real_has_inf hT C1 C2 x)

example (a b : ℝ) : a < b → ¬ (b ≤ a) := by exact fun a_1 ↦ not_le_of_lt a_1

lemma k_in_01 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (k hT C1 C2 x) ∈ Set.Icc 0 1 := by

  intro x
  have h := k_prop hT C1 C2 x
  constructor
  · exact h.right (F_Real_0_is_LB hT C1 C2 x)
  · by_contra c
    simp [k] at c
    let inf := Classical.choose (F_Real_has_inf hT C1 C2 x)
    have inf_def : inf = Classical.choose (F_Real_has_inf hT C1 C2 x) := by rfl
    have inf_prop := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
    rw [← inf_def] at inf_prop c
    simp [IsGLB, IsGreatest] at inf_prop
    cases' inf_prop with inf_lb inf_glb

    let hr := exists_rat_btwn c
    cases' hr with r r_prop

    have r_lb : inclQR r ∈ F_Real hT C1 C2 x
    · apply F_Real_1inf hT C1 C2 x r
      exact_mod_cast r_prop.left

    have aux : inclQR r < inf
    · simp [inclQR]
      exact r_prop.right

    simp [lowerBounds] at inf_lb
    specialize inf_lb r_lb
    apply not_le_of_lt at aux
    exact aux inf_lb


lemma claim1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∈ Closure (H hT C1 C2 p) → (k hT C1 C2 x) ≤ p := by

  intro p x hx
  by_contra c
  simp at c

  simp [k] at c
  let inf := Classical.choose (F_Real_has_inf hT C1 C2 x)
  have inf_def : inf = Classical.choose (F_Real_has_inf hT C1 C2 x) := by rfl
  have inf_prop := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
  rw [← inf_def] at inf_prop c
  simp [IsGLB, IsGreatest] at inf_prop
  cases' inf_prop with inf_lb inf_glb

  let hq := exists_rat_btwn c
  cases' hq with q hq

  have h := (H_Prop hT C1 C2 hC1 hC2 hC1C2).right.right.right p q
    (by exact_mod_cast hq.left)
  apply h at hx

  have aux : inclQR q ∈ F_Real hT C1 C2 x
  · simp [F_Real]
    use q
    simp
    exact hx

  simp [lowerBounds] at inf_lb
  specialize inf_lb aux
  have aux' : inf > q
  · exact_mod_cast hq.right
  apply not_le_of_lt at aux'
  exact aux' inf_lb



lemma claim2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∉ (H hT C1 C2 p) → (k hT C1 C2 x) ≥ p := by

  intro p x hx

  have h : ∀ q : ℚ, q ≤ p → q ∉ (F hT C1 C2 x)
  · intro q hq
    have cases : q = p ∨ q < p := by exact Or.symm (Decidable.lt_or_eq_of_le hq)
    cases' cases with hq hq
    · rw [hq]
      exact hx
    · by_contra c
      simp [F] at c
      have h := (H_Prop hT C1 C2 hC1 hC2 hC1C2).right.right.right q p hq
      apply set_inside_closure at c
      apply h at c
      exact hx c

  have h : ∀ q : ℚ, q ∈ (F hT C1 C2 x) → p < q
  · intro q hq
    by_contra c
    simp at c
    apply h at c
    exact c hq

  simp [k]
  let inf := Classical.choose (F_Real_has_inf hT C1 C2 x)
  have inf_def : inf = Classical.choose (F_Real_has_inf hT C1 C2 x) := by rfl
  have inf_prop := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
  rw [← inf_def] at *
  simp [IsGLB, IsGreatest] at inf_prop
  cases' inf_prop with inf_lb inf_glb

  by_contra c
  simp at c

  have p_inf : inclQR p ∈ lowerBounds (F_Real hT C1 C2 x)
  · intro y hy
    simp [F_Real] at hy
    cases' hy with r hy
    cases' hy with hr hy
    apply h at hr
    rw [← hy]
    simp [inclQR]
    exact le_of_lt hr

  specialize inf_glb p_inf
  apply not_le_of_lt at c
  exact c inf_glb


noncomputable def K {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ((Set.Icc 0 1) : Set ℝ) := fun x ↦ ⟨k hT C1 C2 x, k_in_01 hT C1 C2 x⟩
