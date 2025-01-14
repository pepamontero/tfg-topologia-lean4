import Leantest.Continuous.basic
import Leantest.TopoSpaces.usual

#check Set.image_union

example {X Y : Type} (S : Set (Set X)) (f : X → Y) :
    f '' (⋃₀ S) = ⋃ s ∈ S, f '' s := by
  ext y
  constructor
  all_goals intro hy
  · simp at *
    cases' hy with x hx
    cases' hx with hx1 hx2
    cases' hx1 with s hs
    use s
    constructor
    exact hs.left
    use x
    constructor
    exact hs.right
    exact hx2
  · simp at *
    cases' hy with s hs
    cases' hs.right with x hx
    use x
    constructor
    use s
    constructor
    exact hs.left
    exact hx.left
    exact hx.right



example {X Y : Type} (S : Set (Set Y)) (f : X → Y) :
    f ⁻¹' (⋃₀ S) = ⋃ s ∈ S, f ⁻¹' s := by
  exact Set.preimage_sUnion


def isTopoBase {X : Type} [T : TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)


example [T : TopologicalSpace ℝ] (hT : T = UsualTopology) :
    isTopoBase (⋃ a ∈ ℝ, {x : ℝ | a < x}) := by
  sorry

lemma name {X Y : Type} [T : TopologicalSpace X]
    [T : TopologicalSpace Y] (f : X → Y)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    ContinuousPepa f ↔ ∀ U ∈ B, IsOpen (f ⁻¹' U) := by

  constructor
  all_goals intro h
  · intro U hU
    cases' hB with hB _
    specialize hB U hU
    specialize h U hB
    exact h

  · intro V hV
    cases' hB with _ hB
    specialize hB V hV
    cases' hB with UB hUB
    rw [hUB.right]
    rw [Set.preimage_sUnion]
    apply isOpen_sUnions
    intro U hU

    obtain ⟨S, hS, hU⟩ := Set.mem_sUnion.mp hU


    apply isOpen_sUnion
    intro U hU
    simp at hU
    cases' hU with S hS
    rw [← hS]




    sorry
