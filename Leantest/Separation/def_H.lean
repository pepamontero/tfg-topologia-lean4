import Leantest.Separation.def_G

def H {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : 0 ≤ q ∧ q ≤ 1 then G hT C1 C2 (f_inv ⟨q, h⟩)
  else Set.univ

lemma H_Prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    H hT C1 C2 1 = C2ᶜ ∧
    H hT C1 C2 0 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2) ∧
    (∀ q, IsOpen (H hT C1 C2 q)) ∧
    (∀ p q : ℚ, p < q → Closure (H hT C1 C2 p) ⊆ H hT C1 C2 q)
    := by

  constructor

  · have c : ¬ (1 : ℚ) < (0 : ℚ) := by linarith
    simp [H, c]
    have aux := f_inv_1
    simp at aux
    rw [aux]
    simp [G]

  constructor

  · simp [H]
    have aux := f_inv_0
    simp at aux
    rw [aux]
    have aux : normal_pair (C2ᶜ, C1)
    · constructor; exact hC2
      constructor; exact hC1
      exact hC1C2
    simp [G, from_normality, aux]

  constructor

  · intro q
    have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_le q 0
    cases' cases with hq hq

    · -- q < 0 -> H q = ∅ (trivial)
      simp [H, hq]

    have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
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
      simp [H, aux, aux']

  · intro p q hpq

    have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_le q 0
    cases' cases with hq hq

    · -- q < 0 -> p < q < 0 -> H p = H q = ∅
      have aux : p < 0 := by linarith
      simp [H, aux, hq]
      exact closure_of_empty

    have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
    have aux : ¬ q < 0 := by linarith
    cases' cases with hq' hq'

    · -- 0 ≤ q ≤ 1

      have cases : p < 0 ∨ p ≥ 0 := by exact lt_or_le p 0
      cases' cases with hp hp

      · -- p < 0 -> H p = ∅ (trivial)
        simp [H, hp, closure_of_empty]

      have cases : p ≤ 1 ∨ p > 1 := by exact le_or_lt p 1
      have aux' : ¬ p < 0 := by linarith
      cases' cases with hp' hp'

      · -- 0 ≤ p < q ≤ 1
        simp [H, aux, aux', hp, hp', hq, hq']
        apply G_Prop2' hT C1 C2 hC1 hC2 hC1C2
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
      simp [H, aux, aux', hq, hq']
