import Leantest.Separation.def_F
import Leantest.MyDefs.sets


noncomputable def k {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ℝ :=
    fun x ↦ Classical.choose (F_Real_has_inf hT C1 C2 x)


lemma k_prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x, IsGLB (F_Real hT C1 C2 x) (k hT C1 C2 x) := by

  intro x
  rw [k]
  exact Classical.choose_spec (F_Real_has_inf hT C1 C2 x)



lemma k_in_01 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : ∀ x : X, (k hT C1 C2 x) ∈ Set.Icc 0 1 := by

  intro x
  have ⟨klb, kglb⟩ := k_prop hT C1 C2 x
  constructor
  · exact kglb (F_Real_0_is_LB hT C1 C2 x)
  · by_contra c
    simp at c
    obtain ⟨q, hq1, hqk⟩ := exists_rat_btwn c
    have hq := F_Real_1inf hT C1 C2 x q (by exact_mod_cast hq1)
    apply klb at hq
    apply not_lt.mpr at hq
    exact hq hqk


lemma k_claim1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∈ closure (H hT C1 C2 p) → (k hT C1 C2 x) ≤ p := by

  intro p x hx
  by_contra c
  simp at c
  have ⟨q, hq⟩ := exists_rat_btwn c

  apply H_isOrdered hT C1 C2 hC1 hC2 hC1C2 p q
    (by exact_mod_cast hq.left)
    at hx

  have aux : inclQR q ∈ F_Real hT C1 C2 x
  · simp [F_Real]
    use q
    simp
    exact hx

  have ⟨klb, _⟩ := k_prop hT C1 C2 x
  apply klb at aux
  apply not_lt.mpr at aux
  exact aux hq.right



lemma k_claim2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
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
      have h := H_isOrdered hT C1 C2 hC1 hC2 hC1C2 q p hq
      apply subset_closure at c
      apply h at c
      exact hx c

  have h : ∀ q : ℚ, q ∈ (F hT C1 C2 x) → p < q
  · intro q hq
    by_contra c
    simp at c
    apply h at c
    exact c hq

  obtain ⟨_, kglb⟩ := k_prop hT C1 C2 x
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

  specialize kglb p_inf
  apply not_le_of_lt at c
  exact c kglb


----- COMPORTAMIENTO EN C1

lemma k_in_C1_is_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)
    (hC1_nonempty : C1 ≠ ∅)

    : k hT C1 C2 '' C1 = {0} := by

  ext r
  constructor
  · intro ⟨x, hx, hr⟩
    rw [← hr]
    apply IsGLB.unique (k_prop hT C1 C2 x)
    exact F_Real_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx

  · intro hr
    rw [hr]
    obtain ⟨x, hx⟩ := nonempty_has_element C1 hC1_nonempty
    use x
    constructor
    · exact hx
    · have aux := F_Real_0_GLB_in_C1 hT C1 C2 hC1 hC2 hC1C2 x hx
      have aux' := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
      exact IsGLB.unique aux' aux

lemma k_in_C2_is_1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)
    (hC2_nonempty : C2 ≠ ∅)

    : k hT C1 C2 '' C2 = {1} := by

  ext r
  constructor
  · intro ⟨x, hx, hr⟩
    rw [← hr]
    apply IsGLB.unique (k_prop hT C1 C2 x)
    exact F_Real_1_GLB_in_C2 hT C1 C2 hC1 hC2 hC1C2 x hx

  · intro hr
    simp at hr
    rw [hr]
    simp [k]
    obtain ⟨x, hx⟩ := nonempty_has_element C2 hC2_nonempty
    use x
    constructor
    · exact hx
    · have aux := F_Real_1_GLB_in_C2 hT C1 C2 hC1 hC2 hC1C2 x hx
      have aux' := Classical.choose_spec (F_Real_has_inf hT C1 C2 x)
      exact IsGLB.unique aux' aux
