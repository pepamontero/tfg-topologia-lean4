import Mathlib.Tactic
import Leantest.BasicProp.basic


-- DEFINICIÓN DE INTERIOR DE UN CONJUNTO
def Interior {X : Type} [T : TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∃ U : Set X, OpenNeighbourhood U x ∧ U ⊆ A}


-- CARACTERIZACIÓN DE CONJUNTO ABIERTO
-- (A abierto sii todos sus puntos tienen un entorno abierto contenido en A)
lemma characterization_of_open {X : Type} [T : TopologicalSpace X]
    (A : Set X):
    IsOpen A ↔
    ∀ x ∈ A, ∃ U : Set X, OpenNeighbourhood U x ∧ U ⊆ A := by

  constructor
  all_goals intro h
  · -- ->

    intro x hx
    use A
    constructor
    · constructor
      · exact hx
      · exact h
    · trivial

  · -- <-

    let f : A → Set X := fun x : A ↦ Classical.choose (h x x.property)

    have fdef : ∀ (x : A), f x = Classical.choose (h x x.property)
    intro x
    rfl

    have hA : A = ⋃ (x : A), f x
    ext x
    constructor
    · intro hx
      specialize h x hx

      let hU := Classical.choose_spec h

      specialize fdef ⟨x, hx⟩
      rw [← fdef] at hU

      simp
      use x
      use hx
      exact hU.left.left


    · intro hx
      simp at hx
      cases' hx with y hy
      cases' hy with hy hx

      let hU := Classical.choose_spec (h y hy)

      specialize fdef ⟨y, hy⟩
      rw [← fdef] at hU
      apply hU.right
      exact hx

    -- como A es unión de abiertos entonces es abierto

    rw [hA]
    refine isOpen_iUnion ?mpr.h
    intro x
    let hU := Classical.choose_spec (h x x.property)
    specialize fdef x
    rw [fdef]
    exact hU.left.right


-- EL INTERIOR DE UN CONJUNTO ES UN ABIERTO
lemma interior_is_open {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsOpen (Interior A) := by

  refine (characterization_of_open (Interior A)).mpr ?_
  intro x hx
  rw [Interior] at hx
  simp at hx
  cases' hx with U hU
  use U
  constructor
  · exact hU.left
  · intro y hy
    rw [Interior]
    simp
    use U
    constructor
    · constructor
      · exact hy
      · exact hU.left.right
    · exact hU.right
