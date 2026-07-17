import UrysohnsLemma.BasicProp.open

open TopologicalSpace

/- DEFINITION OF CONTINUOUS FUNCTION -/

-- ANCHOR: continuous_characterization_example
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def
-- ANCHOR_END: continuous_characterization_example


/- COMPOSITION -/

#check Continuous.comp
-- ANCHOR: continuous_comp_example
example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by

  rw [continuous_def] at *
  intro W hW
  specialize hg W hW
  specialize hf (g ⁻¹' W) hg
  exact hf
-- ANCHOR_END: continuous_comp_example

/-
Proposición: son equivalentes:
1. f : X → Y continua
2. ∀ U ⊆ Y con U abierto en X, f⁻¹(U) es abierto en Y
3. ∀ C ⊆ Y con C cerrado en X, f⁻¹(C) es cerrado en Y
-/

#check continuous_iff_isClosed
-- ANCHOR: continuous_iff_isClosed_example
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C) := by
  constructor; all_goals intro h
  · rw [continuous_def] at h
    intro C hC
    rw [← isOpen_compl_iff] at *
    exact h Cᶜ hC

  · rw [continuous_def]
    intro U hU
    rw [← isClosed_compl_iff] at *
    exact h Uᶜ hU
-- ANCHOR_END: continuous_iff_isClosed_example


-- equivalencia con la definición
-- ANCHOR: continuous_neighbourhood_sig
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) :
      (∀ x : X, ∀ V : Set Y,
        Neighbourhood V (f x) → Neighbourhood (f ⁻¹' V) x)
      ↔ ∀ (V : Set Y), IsOpen V → IsOpen (f ⁻¹' V) := by

  constructor; all_goals intro h
-- ANCHOR_END: continuous_neighbourhood_sig

-- ANCHOR: continuous_neighbourhood_forward
  · intro V hVopen
    apply A_open_iff_neighbourhood_of_all.mpr
    intro x hx
    exact h x V
      (by use V; simp; exact ⟨hx, hVopen⟩)
-- ANCHOR_END: continuous_neighbourhood_forward

-- ANCHOR: continuous_neighbourhood_backward
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
-- ANCHOR_END: continuous_neighbourhood_backward
