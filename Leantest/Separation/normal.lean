import Leantest.BasicProp.basic
import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅


#check DiscreteTopo
example {X : Type} (T : TopologicalSpace X)
    (f : X → (Set.Icc 0 1 : Set ℝ)) (hT : T = DiscreteTopo X) :
    ContinuousPepa f := by

  rw [ContinuousPepa]
  intro U hU
  cases' hU with A hA
  sorry

example (f : (Set.Ioo 0 1 : Set ℝ) → (Set.Ioo 0 1: Set ℝ))
    (hf : f x = x) : ContinuousPepa [UsualSpace] [] f := by


  rw [ContinuousPepa]
  intro U hU

  cases' hU with A hA


lemma Uryshon {X : Type} (T : TopologicalSpace X) :
    NormalTopoSpace T ↔  ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ f : X → (Set.Icc 0 1 : Set ℝ), ContinuousPepa f ∧
    f '' C1 = {0} ∧ f '' C2 = {1} := by

  -- Nota: no se si se entiende que [0, 1] es con la usual o que...

  constructor

  · -- →
    intro hT C1 C2 hC1 hC2 hC

    sorry

  · -- ←
    intro hT C1 C2 hC1 hC2 hC
    specialize hT C1 C2 hC1 hC2 hC
    cases' hT with f hf
    cases' hf with hf1 hf2

    use f ⁻¹' Set.Ico 0 (1 / 2)
    sorry
