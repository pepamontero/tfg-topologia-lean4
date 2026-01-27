import Leantest.Separation.def_G

def H {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : 0 ≤ q ∧ q ≤ 1 then G hT C1 C2 (f_inv ⟨q, h⟩)
  else Set.univ


lemma H_value1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : H hT C1 C2 1 = C2ᶜ := by

  have c : ¬ (1 : ℚ) < (0 : ℚ) := by linarith
  simp [H, c]
  have aux := f_inv_1
  simp at aux
  rw [aux]
  simp [G]


lemma H_value0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : H hT C1 C2 0 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2) := by

  simp [H]
  have aux := f_inv_0
  simp at aux
  rw [aux]
  have aux : normal_pair (C2ᶜ, C1)
  · constructor; exact hC2
    constructor; exact hC1
    exact hC1C2
  simp [G, from_normality, aux]


lemma H_isOpen {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : (∀ q, IsOpen (H hT C1 C2 q)) := by

  intro q
  have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_ge q 0
  cases' cases with hq hq

  · -- q < 0 -> H q = ∅ (trivial)
    simp [H, hq]

  have cases : q ≤ 1 ∨ q > 1 := by exact le_or_gt q 1
  have aux : ¬ q < 0 := by linarith
  cases' cases with hq' hq'

  · -- 0 ≤ q ≤ 1 -> usando la prop. de G
    simp [H, aux, hq, hq']
    apply G_Prop1 hT C1 C2 hC1 hC2 hC1C2

  · -- q > 1 -> H q = X (trivial)
    simp [H]
    have aux' : ¬ (0 ≤ q ∧ q ≤ 1)
    · simp at aux
      simp [aux]
      exact hq'
    simp [aux, aux']


lemma H_isOrdered {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : (∀ p q : ℚ, p < q → closure (H hT C1 C2 p) ⊆ H hT C1 C2 q) := by

  intro p q hpq

  have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_ge q 0
  cases' cases with hq hq

  · -- q < 0 -> p < q < 0 -> H p = H q = ∅
    have aux : p < 0 := by linarith
    simp [H, aux, hq]

  have cases : q ≤ 1 ∨ q > 1 := by exact le_or_gt q 1
  have aux : ¬ q < 0 := by linarith
  cases' cases with hq' hq'

  · -- 0 ≤ q ≤ 1

    have cases : p < 0 ∨ p ≥ 0 := by exact lt_or_ge p 0
    cases' cases with hp hp

    · -- p < 0 -> H p = ∅ (trivial)
      simp [H, hp]

    have cases : p ≤ 1 ∨ p > 1 := by exact le_or_gt p 1
    have aux' : ¬ p < 0 := by linarith
    cases' cases with hp' hp'

    · -- 0 ≤ p < q ≤ 1
      simp [H, aux, aux', hp, hp', hq, hq']
      apply G_Prop2_ext hT C1 C2 hC1 hC2 hC1C2
      have hfp := f_inv_prop.right ⟨p, by
        constructor
        exact hp
        exact hp'⟩
      have hfq := f_inv_prop.right ⟨q, by
        constructor
        exact hq
        exact hq'⟩
      rw [hfp, hfq]
      simp
      exact hpq

    · -- p > 1 (imposible)
      linarith

  · -- q > 1 -> H q = X (trivial)
    have aux' : ¬ q ≤ 1 := by linarith
    simp [H, aux, aux', hq]

example {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    H hT C1 C2 1 = C2ᶜ ∧
    H hT C1 C2 0 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2) ∧
    (∀ q, IsOpen (H hT C1 C2 q)) ∧
    (∀ p q : ℚ, p < q → closure (H hT C1 C2 p) ⊆ H hT C1 C2 q)

    := by exact ⟨H_value1 hT C1 C2,
      H_value0 hT C1 C2 hC1 hC2 hC1C2,
      H_isOpen hT C1 C2 hC1 hC2 hC1C2,
      H_isOrdered hT C1 C2 hC1 hC2 hC1C2⟩


----------------- OTRAS PROPIEDADES

lemma H_C1_in_H0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : C1 ⊆ H hT C1 C2 0 := by

  rw [H_value0 hT C1 C2 hC1 hC2 hC1C2]
  exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.left

lemma H_ClosureH0_in_C2c {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : closure (H hT C1 C2 0) ⊆ C2ᶜ := by

  rw [H_value0 hT C1 C2 hC1 hC2 hC1C2]
  exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.right


lemma H_at_bt1_is_univ {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    : ∀ q > 1, H hT C1 C2 q = Set.univ := by
  intro q hq
  have aux1 : ¬ q < 0 := by linarith
  have aux2 : ¬ (0 ≤ q ∧ q ≤ 1)
  · by_contra c
    cases' c with c c
    · exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hq c
  simp [H, aux1, aux2]
