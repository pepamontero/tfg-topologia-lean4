import Leantest.Separation.lemmas
import Leantest.Continuous.subspaces

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
