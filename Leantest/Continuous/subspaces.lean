import Leantest.Continuous.basic


/-
  Result:
    X, Y spaces, Z ⊆ Y subspace
    f : X → Z is continuous iff
      the condition of continuity is true for opens in Y
-/

lemma continuousInSubspace_iff_trueForSpace {X Y : Type} {Z : Set Y}
    [TX : TopologicalSpace X] [TY : TopologicalSpace Y]
    [TZ : TopologicalSpace Z] (hZ : TZ = TopoSubspace TY Z)
    (f : X → Z) :
    ContinuousPepa f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' (Subtype.val ⁻¹' U)) := by

  constructor
  all_goals intro h U hU

  · -- →
    apply h
    rw [hZ]
    use U
    constructor
    · exact hU
    · simp
      exact Set.inter_comm Z U

  · -- ←
    rw [hZ] at hU
    cases' hU with V hV

    have aux : Subtype.val ⁻¹' (Subtype.val '' U) = U
    exact Set.preimage_val_image_val_eq_self

    rw [← aux]
    rw [hV.right]
    simp
    apply h
    exact hV.left
