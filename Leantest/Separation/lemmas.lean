import Leantest.Continuous.basic
import Leantest.TopoSpaces.usual
import Leantest.BasicProp.subspaces

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


/-
example [T : TopologicalSpace ℝ] (hT : T = UsualTopology) :
    isTopoBase (⋃ a ∈ ℝ, {x : ℝ | a < x}) := by
  sorry
-/

lemma continuous_iff_trueForBasics {X Y : Type} [T : TopologicalSpace X]
    [T' : TopologicalSpace Y] (f : X → Y)
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
    apply isOpen_sUnion
    intro U hU

    sorry

example {X Y : Type} (f : X → Y) (x1 x2 : X) (h : x1 = x2) : f x1 = f x2 := by exact congrArg f h


example {X Y : Type} (f : X → Y) (x1 x2 : Set X) (h : x1 = x2) : f '' x1 = f '' x2 := by
  exact congrArg (Set.image f) h


lemma continuousInSubspace_iff_trueForSpace' {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z) :
    ContinuousPepa f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

  constructor
  all_goals intro h U hU

  · apply h
    rw [hZ]
    use U
    constructor
    · exact hU
    · simp
      exact Set.inter_comm Z U

  · rw [hZ] at hU
    cases' hU with V hV

    have aux : Subtype.val ⁻¹' (Subtype.val '' U) = U
    exact Set.preimage_val_image_val_eq_self

    rw [← aux]
    rw [hV.right]
    simp
    apply h
    exact hV.left
