import UrysohnsLemma.TopoSpaces.usual


/-
    DEF: Given B ⊆ P(X), is B a Base for X?
-/

-- ANCHOR: isTopoBase_def
def isTopoBase {X : Type} [TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)
-- ANCHOR_END: isTopoBase_def


/-
Example:
  B = {(a, b) : a, b ∈ ℝ} is a Base for ℝ with the Usual Topology
-/

-- ANCHOR: BaseOfRealTopo_forward
lemma BaseOfRealTopo [T : TopologicalSpace ℝ]
    (hT : T = UsualTopology) :
    isTopoBase {s | ∃ a b : ℝ, s = Set.Ioo a b} := by
  constructor
  · intro U hU
    obtain ⟨a, b, hU⟩ := hU
    rw [hU, hT]
    exact ioo_open_in_R a b
-- ANCHOR_END: BaseOfRealTopo_forward

-- ANCHOR: BaseOfRealTopo_backward_start
  · intro U hUopen
    rw [hT] at hUopen
-- ANCHOR_END: BaseOfRealTopo_backward_start

-- ANCHOR: BaseOfRealTopo_delta
    let δ : U → ℝ := fun x ↦ Classical.choose (hUopen x x.property)
    have δspec : ∀ x : U, 0 < δ x
        ∧ ∀ y : ℝ, ↑x - δ x < y ∧ y < ↑x + δ x → y ∈ U :=
      fun x ↦ Classical.choose_spec (hUopen x (x.property))

    use {s | ∃ x, s = Set.Ioo (x - δ x) (x + δ x)}
-- ANCHOR_END: BaseOfRealTopo_delta

-- ANCHOR: BaseOfRealTopo_subset_B
    constructor

    · intro V hV
      obtain ⟨x, hV⟩ := hV
      use (↑x - δ x), (↑x + δ x)
-- ANCHOR_END: BaseOfRealTopo_subset_B

-- ANCHOR: BaseOfRealTopo_ext_u
    · ext u; constructor; all_goals intro hu
-- ANCHOR_END: BaseOfRealTopo_ext_u
-- ANCHOR: BaseOfRealTopo_forward_incl
      · use Set.Ioo (↑u - δ ⟨u, hu⟩) (↑u + δ ⟨u, hu⟩)
        constructor
        · simp
          use u, hu
        · simp
          exact (δspec ⟨u, hu⟩).left
-- ANCHOR_END: BaseOfRealTopo_forward_incl

-- ANCHOR: BaseOfRealTopo_backward_incl
      · obtain ⟨I, hI, hu⟩ := hu
        obtain ⟨v, hI⟩ := hI
        rw [hI] at hu
        exact (δspec v).right u hu
-- ANCHOR_END: BaseOfRealTopo_backward_incl
