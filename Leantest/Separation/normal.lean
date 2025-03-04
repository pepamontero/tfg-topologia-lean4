import Leantest.BasicProp.basic
import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.usual
import Leantest.BasicProp.subspaces
import Leantest.BasicProp.closure
import Leantest.BasicProp.interior
import Leantest.Separation.lemmas
import Leantest.MyDefs.my_inf
import Leantest.MyDefs.sets


set_option diagnostics true
set_option diagnostics.threshold 5000


/-
      DEF: ESPACIO NORMAL
-/

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅


/-
      CHARACTERIZATION OF NORMAL
  `(X, T)` is a Normal topological space iff
    `∀ U ⊆ X` open, `∀ C ⊆ X` closed with `C ⊆ U`,
    `∃ V ⊆ X` open,, `C ⊆ V ⊆ Closure(V) ⊆ U`
-/

lemma characterization_of_normal {X : Type}
    (T : TopologicalSpace X) :
    NormalTopoSpace T ↔
    ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (Closure V) ⊆ U := by

  constructor
  · intro hT U C hU hC hCU

    have hUc : IsClosed Uᶜ
    exact isClosed_compl_iff.mpr hU

    have hCUc : C ∩ Uᶜ = ∅
    rw [ABdisjoint_iff_AsubsBc]
    simp
    exact hCU

    specialize hT C Uᶜ hC hUc hCUc
    cases' hT with V1 h
    cases' h with V2 h
    use V1
    constructor
    · exact h.left
    · constructor
      · exact h.right.right.left
      · rw [← compl_compl U]
        rw [← ABdisjoint_iff_AsubsBc]

        have aux : Closure V1 ∩ V2 = ∅
        exact disjointU_V_then_disjointClosureU_V h.right.left h.right.right.right.right

        ext x
        constructor
        · intro hx
          cases' hx with hA hC
          apply h.right.right.right.left at hC
          rw [← aux]
          constructor
          exact hA
          exact hC
        · intro hx
          by_contra
          exact hx

  · intro h C1 C2 hC1 hC2 hC

    have hC' : C2 ⊆ C1ᶜ
    rw [← ABdisjoint_iff_AsubsBc]
    rw [Set.inter_comm C2 C1]
    exact hC

    specialize h C1ᶜ C2 (by exact IsClosed.isOpen_compl) hC2 hC'
    cases' h with V hV

    use (Closure V)ᶜ
    use V

    constructor
    · simp
      exact closure_is_closed V
    · constructor
      · exact hV.left
      · constructor
        · rw [← ABdisjoint_iff_AsubsBc]
          rw [Set.inter_comm C1 (Closure V)]
          rw [ABdisjoint_iff_AsubsBc]
          exact hV.right.right
        · constructor
          · exact hV.right.left
          · rw [Set.inter_comm (Closure V)ᶜ V]
            rw [ABdisjoint_iff_AsubsBc]
            simp
            exact set_inside_closure V
