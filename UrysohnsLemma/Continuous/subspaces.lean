import UrysohnsLemma.Continuous.basic
import UrysohnsLemma.BasicProp.subspaces


/-
  Result:
    X, Y spaces, Z ⊆ Y subspace
    f : X → Z is continuous iff
      the condition of continuity is true for opens in Y
-/

example {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z)  :
    Continuous f ↔ ∀ U : Set Y, TY.IsOpen U → TX.IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by
  sorry

-- ANCHOR: continuousInSubspace_iff_trueForSpace_sig
lemma continuousInSubspace_iff_trueForSpace {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z) :
    Continuous f ↔ ∀ U : Set Y, TY.IsOpen U → TX.IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

  rw [continuous_def]
  constructor
  all_goals intro h U hU
-- ANCHOR_END: continuousInSubspace_iff_trueForSpace_sig

-- ANCHOR: continuousInSubspace_iff_trueForSpace_forward
  · -- →
    apply h
    rw [hZ]
    use U
    constructor
    · exact hU
    · simp
      exact Set.inter_comm Z U
-- ANCHOR_END: continuousInSubspace_iff_trueForSpace_forward

-- ANCHOR: continuousInSubspace_iff_trueForSpace_backward
  · -- ←
    rw [hZ] at hU
    obtain ⟨V, hV⟩ := hU

    rw [← @Set.preimage_val_image_val_eq_self Y Z U, hV.right]
    simp
    apply h
    exact hV.left
-- ANCHOR_END: continuousInSubspace_iff_trueForSpace_backward
