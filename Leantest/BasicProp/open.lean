import Leantest.BasicProp.basic


/-
  CHARACTERIZATION OF OPEN
U ⊆ X is Open in X if it is Neighbourhood of all its points
-/

lemma A_open_iff_neighbourhood_of_all
    {X : Type} [T : TopologicalSpace X]
    {A : Set X} : IsOpen A ↔
    ∀ x ∈ A, Neighbourhood A x := by
  constructor
  all_goals intro h

  · -- →
    intro x hx
    use A
    constructor
    · trivial
    · constructor
      · exact hx
      · exact h

  · -- ←
    have hUnion : A = ⋃ a : A, Classical.choose (h a a.property)
    · ext x; constructor; all_goals intro hx
      · have ⟨_, hUx⟩  := Classical.choose_spec (h x hx)
        simp
        use x, hx
        exact hUx.left
      · simp at hx
        obtain ⟨a, ha, hx⟩ := hx
        have ⟨ha', _⟩ := Classical.choose_spec (h a ha)
        apply ha'
        exact hx

    rw [hUnion]
    apply isOpen_iUnion
    intro a
    exact (Classical.choose_spec (h a a.property)).right.right
