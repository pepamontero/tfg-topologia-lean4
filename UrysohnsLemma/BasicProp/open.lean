import UrysohnsLemma.BasicProp.basic


/-
  CHARACTERIZATION OF OPEN
U ⊆ X is Open in X if it is Neighbourhood of all its points
-/

-- ANCHOR: A_open_iff_neighbourhood_of_all_sig
lemma A_open_iff_neighbourhood_of_all
    {X : Type} [T : TopologicalSpace X]
    {A : Set X} : IsOpen A ↔
    ∀ x ∈ A, Neighbourhood A x := by
-- ANCHOR_END: A_open_iff_neighbourhood_of_all_sig
-- ANCHOR: A_open_iff_constructor
  constructor
  all_goals intro h
-- ANCHOR_END: A_open_iff_constructor

-- ANCHOR: A_open_iff_forward
  · -- →
    intro x hx
    use A
    constructor
    · trivial
    · constructor
      · exact hx
      · exact h
-- ANCHOR_END: A_open_iff_forward

-- ANCHOR: A_open_iff_backward_hUnion_stmt
  · -- ←
    have hUnion : A = ⋃ a : A, Classical.choose (h a a.property)
-- ANCHOR_END: A_open_iff_backward_hUnion_stmt
-- ANCHOR: A_open_iff_backward_hUnion_forward
    · ext x; constructor; all_goals intro hx
      · have ⟨_, hUx⟩  := Classical.choose_spec (h x hx)
        simp
        use x, hx
        exact hUx.left
-- ANCHOR_END: A_open_iff_backward_hUnion_forward
-- ANCHOR: A_open_iff_backward_hUnion_backward
      · simp at hx
        obtain ⟨a, ha, hx⟩ := hx
        have ⟨ha', _⟩ := Classical.choose_spec (h a ha)
        apply ha'
        exact hx
-- ANCHOR_END: A_open_iff_backward_hUnion_backward

-- ANCHOR: A_open_iff_backward_finish
    rw [hUnion]
    apply isOpen_iUnion
    intro a
    exact (Classical.choose_spec (h a a.property)).right.right
-- ANCHOR_END: A_open_iff_backward_finish
