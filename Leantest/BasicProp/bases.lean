import Leantest.TopoSpaces.usual


/-
    DEF: Given B ⊆ P(X), is B a Base for X?
-/

def isTopoBase {X : Type} [TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)


/-
Example:
  B = {(a, b) : a, b ∈ ℝ} is a Base for ℝ with the Usual Topology
-/

lemma BaseOfRealTopo [T : TopologicalSpace ℝ]
    (hT : T = UsualTopology) :
    isTopoBase {s | ∃ a b : ℝ, s = Set.Ioo a b} := by
  constructor
  · intro U hU
    obtain ⟨a, b, hU⟩ := hU
    rw [hU, hT]
    exact ioo_open_in_R a b

  · intro U hUopen
    rw [hT] at hUopen

    let δ : U → ℝ := fun x ↦ Classical.choose (hUopen x x.property)
    have δspec : ∀ x : U, 0 < δ x ∧ ∀ y : ℝ, ↑x - δ x < y ∧ y < ↑x + δ x → y ∈ U := fun x ↦ Classical.choose_spec (hUopen x (x.property))

    use {s | ∃ x, s = Set.Ioo (x - δ x) (x + δ x)}

    constructor

    · intro V hV
      obtain ⟨x, hV⟩ := hV
      use (↑x - δ x), (↑x + δ x)

    · ext u; constructor; all_goals intro hu
      · use Set.Ioo (↑u - δ ⟨u, hu⟩) (↑u + δ ⟨u, hu⟩)
        constructor
        · simp
          use u, hu
        · simp
          exact (δspec ⟨u, hu⟩).left

      · obtain ⟨I, hI, hu⟩ := hu
        obtain ⟨v, hI⟩ := hI
        rw [hI] at hu
        exact (δspec v).right u hu
