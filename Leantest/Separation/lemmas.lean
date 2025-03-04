import Leantest.Continuous.basic
import Leantest.TopoSpaces.usual
import Leantest.BasicProp.subspaces
import Leantest.Separation.hausdorff


example {X Y : Type} (S : Set (Set Y)) (f : X → Y) :
    f ⁻¹' (⋃₀ S) = ⋃ s ∈ S, f ⁻¹' s := by
  exact Set.preimage_sUnion

example {X Y : Type} (S : Set (Set Y)) (f : X → Y) :
    f ⁻¹' (⋃ s ∈ S, s) = ⋃ s ∈ S, f ⁻¹' s := by
  exact Set.preimage_iUnion₂


def isTopoBase {X : Type} [T : TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)



lemma BaseOfRealTopo [T : TopologicalSpace ℝ] (hT : T = UsualTopology)
    (f : ℝ × ℝ → Set ℝ) (hf : ∀ a b : ℝ, f (a, b) = Set.Ioo a b) :
    isTopoBase (f '' (Set.univ)) := by

  constructor

  · intro U hU
    simp at hU
    cases' hU with a hU
    cases' hU with b hU
    rw [hf a b] at hU
    rw [← hU]
    exact is_open_open_interval hT a b

  · intro V hV
    rw [hT] at hV

    have aux : ∀ x ∈ V, ∃ δ > 0, ∀ (y : ℝ), x - δ < y ∧ y < x + δ → y ∈ V
    exact fun x a ↦ hV x a

    let g : V → ℝ := fun x : V ↦ Classical.choose (aux x x.property)


    have g_spec : ∀ x : V, 0 < g x ∧ ∀ y : ℝ, ↑x - g x < y ∧ y < ↑x + g x → y ∈ V :=
      fun x ↦ Classical.choose_spec (aux x (x.property))

    let new_g : V → Set ℝ := fun x : V ↦ Set.Ioo (x - g x) (x + g x)
    have new_g_def : ∀ x : V, new_g x = Set.Ioo (x - g x) (x + g x)
    exact fun x ↦ rfl

    -- new_g nos da, para cada x, el intervalo (x - δ, x + δ)
    -- donde el δ sale de la definición de V abierto en ℝ aplicada en x

    use new_g '' (Set.univ)
    -- utilizamos la unión de estos conjuntos

    constructor

    · intro A hA
      simp
      simp at hA
      cases' hA with a hA
      cases' hA with ha hA
      rw [new_g_def] at hA
      use (a - g ⟨a, ha⟩)
      use (a + g ⟨a, ha⟩)
      specialize hf (a - g ⟨a, ha⟩) (a + g ⟨a, ha⟩)
      rw [hf]
      rw [← hA]

    · ext x
      constructor
      all_goals intro hx
      · simp
        use x
        use hx

        rw [new_g_def]
        simp
        specialize g_spec ⟨x, hx⟩
        exact g_spec.left
      · simp at hx
        cases' hx with y hy
        cases' hy with hy hx

        specialize g_spec ⟨y, hy⟩
        cases' g_spec with hδ h
        specialize h x
        apply h
        exact hx


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



example {X Y : Type} (f : X → Y) (x1 x2 : X) (h : x1 = x2) : f x1 = f x2 := by exact congrArg f h


example {X Y : Type} (f : X → Y) (x1 x2 : Set X) (h : x1 = x2) : f '' x1 = f '' x2 := by
  exact congrArg (Set.image f) h


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
