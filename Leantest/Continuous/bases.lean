import Leantest.BasicProp.bases
import Leantest.Continuous.subspaces

open Leantest.Basic
/-
  Result:
    f : X → Y is continuous iff
      the condition of continuity is true for Basic sets
-/

lemma continuous_iff_trueForBasics {X Y : Type} [T : TopologicalSpace X]
    [T' : TopologicalSpace Y] (f : X → Y)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    Continuous f ↔ ∀ U ∈ B, IsOpen (f ⁻¹' U) := by
  rw [continuous_def]
  constructor; all_goals intro h
  · exact fun U hU ↦ h U (hB.left U hU)
  · intro V hV
    obtain ⟨UB, hUB⟩ := hB.right V hV
    rw [hUB.right, Set.preimage_sUnion]
    apply isOpen_biUnion
    intro A hA
    apply h
    exact (hUB.left hA)



lemma continuousInSubspace_iff_trueForBase {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z)
    (B : Set (Set Y)) (hB : isTopoBase B) :
    Continuous f ↔ ∀ U : Set Y, U ∈ B → IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

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
