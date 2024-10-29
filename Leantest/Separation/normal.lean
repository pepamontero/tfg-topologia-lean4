import Leantest.BasicProp.basic
import Leantest.Continuous.basic

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅

lemma Uryshon {X : Type} (T : TopologicalSpace X) :
    NormalTopoSpace T ↔  ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ f : X → Set.Icc 0 1, ContinuousPepa f ∧
    f '' C1 = {0} ∧ f '' C2 = {1} := by

  constructor

  · -- → (esta es fácil)
    sorry

  · -- ←
    sorry
