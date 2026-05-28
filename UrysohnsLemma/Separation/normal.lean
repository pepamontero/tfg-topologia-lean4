import Mathlib.Tactic

/-
      DEF: ESPACIO NORMAL
-/

#check NormalSpace
#print NormalSpace.normal -- Def. espacio normal

lemma normal_space_def {X : Type} (T : TopologicalSpace X) :
  NormalSpace X ↔ ∀ C : Set X, ∀ D : Set X,
    IsClosed C → IsClosed D → Disjoint C D →
    ∃ U : Set X, ∃ V : Set X, IsOpen U ∧ IsOpen V ∧
    C ⊆ U ∧ D ⊆ V ∧ Disjoint U V := by
  constructor
  · intro h
    have h := h.normal
    intro s t hs ht hst
    specialize h s t hs ht hst
    obtain ⟨U, V, hU, hV, h1, h2, h3⟩ := h
    use U
    use V

  · intro h
    exact { normal := by
      {
        intro s t hs ht hst
        specialize h s t hs ht hst
        obtain ⟨U, V, hU, hV, h1, h2, h3⟩ := h
        use U
        use V
      }
    }


/-
      CHARACTERIZATION OF NORMAL
  `(X, T)` is a Normal topological space iff
    `∀ U ⊆ X` open, `∀ C ⊆ X` closed with `C ⊆ U`,
    `∃ V ⊆ X` open,, `C ⊆ V ⊆ closure(V) ⊆ U`
-/

lemma characterization_of_normal {X : Type}
    (T : TopologicalSpace X) :
    NormalSpace X ↔
    ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (closure V) ⊆ U := by

  rw [normal_space_def]
  constructor
  · intro hT U C hU hC hCU

    obtain ⟨V1, V2, V1_open, V2_open, hCV, hUV, hV⟩ :=
      hT C Uᶜ
      hC
      (by exact isClosed_compl_iff.mpr hU)
      (by rw [← Set.subset_compl_iff_disjoint_right, compl_compl]; exact hCU)

    use V1
    constructor
    · exact V1_open
    constructor
    · exact hCV
    · trans V2ᶜ; swap
      · exact Set.compl_subset_comm.mp hUV
      · apply Disjoint.closure_left at hV
        specialize hV V2_open
        exact Set.subset_compl_iff_disjoint_right.mpr hV


  · intro h C1 C2 C1_closed C2_closed hC

    obtain ⟨V, V_open, hV⟩ :=
      h C1ᶜ C2
      (by exact IsClosed.isOpen_compl)
      C2_closed
      (by rw [Set.subset_compl_iff_disjoint_left]; exact hC)

    use (closure V)ᶜ
    use V

    constructor
    · apply isOpen_compl_iff.mpr
      exact isClosed_closure
    constructor
    · exact V_open
    constructor
    · apply Set.subset_compl_comm.mp
      exact hV.right
    constructor
    · exact hV.left
    · rw [← Set.subset_compl_iff_disjoint_left, compl_compl]
      exact subset_closure
