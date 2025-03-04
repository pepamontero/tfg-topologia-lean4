import Leantest.Continuous.basic
import Leantest.TopoSpaces.usual
set_option linter.unusedVariables false


/-
    DEF: Given B ⊆ P(X), is B a Base for X?
-/

def isTopoBase {X : Type} [T : TopologicalSpace X]
    (B : Set (Set X)) : Prop :=
  (∀ U ∈ B, IsOpen U) ∧
  (∀ V : Set X, IsOpen V → ∃ UB ⊆ B, V = ⋃₀ UB)


/-
Example:
  B = {(a, b) : a, b ∈ ℝ} is a Base for ℝ with the Usual Topology
-/

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
    rw [hT]
    apply ioo_open_in_R a b

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
