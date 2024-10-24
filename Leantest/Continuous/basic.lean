import Mathlib.Tactic

open TopologicalSpace

/- DEFINITION OF CONTINUOUS FUNCTION -/



example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    Continuous f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  exact continuous_def

/-
Osea que esto igual lo reescribo desde 0 ajaja
-/

def ContinuousPepa {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
    ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U)

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    ContinuousPepa f ↔ ∀ U : Set Y, IsOpen U → IsOpen (f ⁻¹' U) := by
  rfl

-- no se habrá que ver si lo re escribo o que

/- COMPOSITION -/

example (X Y Z : Type) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by

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

/-
Proposición: Sean
- f : X → Y continua
- Z ⊆ X
Entonces f : Z → Y es continua
-/

#check Set.restrict

example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (Z : Set X) (hf : Continuous f) :
    Continuous (Z.restrict f) := by

  rw [continuous_def] at *
  intro s hs
  specialize hf s hs

  sorry -- creo que paso pq usa muchas movidas de subespacios
