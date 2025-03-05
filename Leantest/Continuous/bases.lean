import Leantest.BasicProp.bases
import Leantest.Continuous.subspaces


/-
  Result:
    f : X → Y is continuous iff
      the condition of continuity is true for Basic sets
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
    cases' hB with hB1 hB
    specialize hB V hV
    cases' hB with UB hUB
    rw [hUB.right]
    rw [Set.preimage_sUnion]

    apply isOpen_biUnion
    intro A hA
    apply h
    apply hUB.left
    exact hA



lemma continuousInSubspace_iff_trueForBase {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    ContinuousPepa f ↔ ∀ U : Set Y, U ∈ B → IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

  constructor
  all_goals intro h

  · -- →
    rw [continuousInSubspace_iff_trueForSpace hZ] at h
    intro U hU
    apply h
    exact hB.left U hU

  · -- ←
    rw [continuousInSubspace_iff_trueForSpace hZ]
    intro U hU

    rw [isTopoBase] at hB
    cases' hB with hB1 hB2

    specialize hB2 U hU
    cases' hB2 with UB hUB
    rw [hUB.right]


    rw [Set.preimage_sUnion]
    rw [Set.preimage_iUnion₂]

    apply isOpen_biUnion
    intro A hA
    apply h
    apply hUB.left
    exact hA
