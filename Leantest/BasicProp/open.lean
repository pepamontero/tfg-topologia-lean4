import Leantest.BasicProp.basic


/-
  CHARACTERIZATION OF OPEN
U ⊆ X is Open in X if it's Open Neighbourhood of all its points
-/

lemma A_open_iff_neighbourhood_of_all
    {X : Type} [T : TopologicalSpace X]
    (A : Set X) : IsOpen A ↔
    ∀ x ∈ A, Neighbourhood A x := by
  constructor
  all_goals intro h
  · -- →
    intro x hx
    use A
    constructor
    trivial
    constructor
    exact hx
    exact h

  · -- ←
    -- classical choose?
    have h : ∀ a : X, a ∈ A → ∃ Ua : Set X, (Ua ⊆ A ∧ OpenNeighbourhood Ua a)
    · exact h

    have aux : A = ∅ ∨ ¬ (A = ∅)
    exact Classical.em (A = ∅)

    cases' aux with h1 h2

    · -- A is empty
      rw [h1]
      exact isOpen_empty

    · -- A is not empty
      --let g : A → Set X := fun a : A ↦ Classical.choose (h a a.property)

      have hUnion : A = ⋃ a : A, Classical.choose (h a a.property)
      · ext x ; constructor <;> intro hx
        · let hx' := Classical.choose_spec (h x hx)
          simp
          use x
          use hx
          exact hx'.right.left
        · simp at hx
          cases' hx with y hy
          cases' hy with hy hx
          let m := Classical.choose_spec (h y hy)
          apply m.left
          exact hx

      rw [hUnion]

      have hOpen : ∀ a : A, IsOpen (Classical.choose (h a a.property))
      · intro a
        let ha := Classical.choose_spec (h a a.property)
        exact ha.right.right

      exact isOpen_iUnion hOpen


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
