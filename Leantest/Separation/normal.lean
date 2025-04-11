import Leantest.BasicProp.closure

/-
      DEF: ESPACIO NORMAL
-/

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C : Set X, ∀ D : Set X,
    IsClosed C → IsClosed D → C ∩ D = ∅ →
    ∃ U : Set X, ∃ V : Set X, IsOpen U ∧ IsOpen V ∧
    C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅


/-
      CHARACTERIZATION OF NORMAL
  `(X, T)` is a Normal topological space iff
    `∀ U ⊆ X` open, `∀ C ⊆ X` closed with `C ⊆ U`,
    `∃ V ⊆ X` open,, `C ⊆ V ⊆ Closure(V) ⊆ U`
-/

example {X : Type} :  ¬ (Set.Nonempty (∅ : Set X))  := by refine Set.not_nonempty_empty

example {X : Type} (A : Set X) : A.Nonempty ↔ A ≠ ∅ := by exact Set.nonempty_iff_ne_empty
example {X : Type} (A : Set X) : ¬ A.Nonempty ↔ A = ∅ := by exact Set.not_nonempty_iff_eq_empty
#check Set.disjoint_iff_inter_eq_empty
example {X : Type} (A B : Set X) : Disjoint A B ↔ Disjoint B A := by exact disjoint_comm

example {X : Type} (A B : Set X) : A ⊆ Bᶜ ↔ B ⊆ Aᶜ := by exact Set.subset_compl_comm
example {X : Type} (A B : Set X) : A ∩ B = B ∩ A := by exact Set.inter_comm A B


lemma characterization_of_normal {X : Type}
    (T : TopologicalSpace X) :
    NormalTopoSpace T ↔
    ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (Closure V) ⊆ U := by

  constructor
  · intro hT U C hU hC hCU

    obtain ⟨V1, V2, V1_open, V2_open, hCV, hUV, hV⟩ :=
      hT C Uᶜ
      hC
      (by exact isClosed_compl_iff.mpr hU)
      (by rw [ABdisjoint_iff_AsubsBc, compl_compl]; exact hCU)

    use V1
    constructor
    · exact V1_open
    constructor
    · exact hCV
    · apply disjointU_V_then_disjointClosureU_V V2_open at hV
      apply Set.disjoint_iff_inter_eq_empty.mpr at hV -- usamos la propiedad Disjoint de Lean
      apply Set.disjoint_compl_right_iff_subset.mp
      exact Set.disjoint_of_subset_right hUV hV

  · intro h C1 C2 C1_closed C2_closed hC

    obtain ⟨V, V_open, hV⟩ :=
      h C1ᶜ C2
      (by exact IsClosed.isOpen_compl)
      C2_closed
      (by rw [← ABdisjoint_iff_AsubsBc, Set.inter_comm C2 C1]; exact hC)

    use (Closure V)ᶜ
    use V

    constructor
    · simp
      exact closure_is_closed V
    constructor
    · exact V_open
    constructor
    · apply Set.subset_compl_comm.mp
      exact hV.right
    constructor
    · exact hV.left
    · rw [Set.inter_comm]
      rw [ABdisjoint_iff_AsubsBc]
      simp
      exact set_inside_closure V
