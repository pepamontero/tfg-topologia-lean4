import Mathlib.Tactic
import Leantest.BasicProp.open

open TopologicalSpace

/- DEFINITION OF CONTINUOUS FUNCTION -/

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def


/- COMPOSITION -/

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  --exact Continuous.comp hg hf

  rw [continuous_def] at *
  intro s hs
  specialize hg s hs
  specialize hf (g ⁻¹' s) hg
  exact hf

/-
Proposición: son equivalentes:
1. f : X → Y continua
2. ∀ U ⊆ Y con U abierto en X, f⁻¹(U) es abierto en Y
3. ∀ C ⊆ Y con C cerrado en X, f⁻¹(C) es cerrado en Y
-/

#check continuous_iff_isClosed
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C) := by
  constructor <;> intro h
  · rw [continuous_def] at h
    intro C hC
    rw [← isOpen_compl_iff] at *
    specialize h Cᶜ hC
    exact h

  · rw [continuous_def]
    intro s hs
    rw [← compl_compl s] at hs
    rw [isOpen_compl_iff] at hs
    specialize h sᶜ hs
    simp at h
    exact h


-- equivalencia con la definición
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
      (∀ x : X, ∀ V : Set Y,
        Neighbourhood V (f x) → Neighbourhood (f ⁻¹' V) x)
      ↔ ∀ (V : Set Y), IsOpen V → IsOpen (f ⁻¹' V) := by

  constructor; all_goals intro h

  · intro V hVopen
    apply A_open_iff_neighbourhood_of_all.mpr
    intro x hx
    exact h x V
      (by use V; simp; exact ⟨hx, hVopen⟩)

  · intro x V hV
    obtain ⟨U, hUV, hU⟩ := hV
    obtain ⟨hUx, hUopen⟩ := hU
    use f ⁻¹' U
    constructor
    · intro u hu
      apply hUV
      exact hu
    · constructor
      · exact hUx
      · exact h U hUopen
