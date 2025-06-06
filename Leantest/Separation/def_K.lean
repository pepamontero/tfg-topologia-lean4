import Leantest.Separation.def_k

noncomputable def K {X : Type} [TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    : X → ((Set.Icc 0 1) : Set ℝ) := fun x ↦ ⟨k hT C1 C2 x, k_in_01 hT C1 C2 x⟩


lemma f_claim1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∈ closure (H hT C1 C2 p) → Subtype.val (K hT C1 C2 x) ≤ p := by
  exact fun p x a ↦ k_claim1 hT C1 C2 hC1 hC2 hC1C2 p x a

lemma f_claim2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, ∀ x : X, x ∉ (H hT C1 C2 p) → Subtype.val (K hT C1 C2 x) ≥ p := by
  exact fun p x a ↦ k_claim2 hT C1 C2 hC1 hC2 hC1C2 p x a


lemma K_in_C1_is_0 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (C1 C2 : Set X)

    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ x : X, x ∈ C1 → K hT C1 C2 x = 0 := by
  have aux := k_in_C1_is_0 hT C1 C2 hC1 hC2 hC1C2
  simp [K]
  intro x hx
  specialize aux x hx
  exact Eq.symm (SetCoe.ext (id (Eq.symm aux)))
