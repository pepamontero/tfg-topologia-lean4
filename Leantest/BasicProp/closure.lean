import Leantest.BasicProp.basic
import Leantest.BasicProp.interior

#check closure

-- DEFINICIÓN DE CLAUSURA DE UN CONJUNTO
def Closure {X : Type} [TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∀ V : Set X, Neighbourhood V x → V ∩ A ≠ ∅}

lemma my_closure  {X : Type} [T : TopologicalSpace X] (A : Set X) : Closure A = closure A := by
  ext x
  constructor

  · intro h
    rw [mem_closure_iff]
    simp [Closure] at h
    intro V hV hVx
    have h' : Neighbourhood V x
    · rw [Neighbourhood]
      use V
      simp
      rw [OpenNeighbourhood]
      exact ⟨hVx, hV⟩
    specialize h V h'
    exact Set.nonempty_iff_ne_empty.mpr h

  · intro h
    rw [mem_closure_iff] at h
    rw [Closure]
    simp
    intro V hV
    rw [Neighbourhood] at hV
    obtain ⟨U , hU⟩ := hV
    rw [OpenNeighbourhood] at hU
    specialize h U hU.right.right hU.right.left
    have aux : U ∩ A ⊆ V ∩ A
    · exact Set.inter_subset_inter hU.left fun ⦃a⦄ a ↦ a
    have aux : (V ∩ A).Nonempty
    · exact Set.Nonempty.mono aux h
    exact Set.nonempty_iff_ne_empty.mp aux



-- T: A está contenido en su clausura

#check subset_closure
lemma set_inside_closure {X : Type} [T : TopologicalSpace X] (A : Set X) :
    A ⊆ Closure A := by

  intro x hx
  intro V hV
  by_contra hc

  have hc' : x ∈ V ∩ A
  constructor
  · cases' hV with U hU
    apply hU.left
    exact hU.right.left
  · exact hx

  rw [hc] at hc'
  exact hc'

#check Set.subset_compl_iff_disjoint_right
lemma ABdisjoint_iff_AsubsBc {X : Type} {A B : Set X} :
    A ∩ B = ∅ ↔ A ⊆ Bᶜ := by

  constructor
  · intro h y hy
    by_contra hy'
    simp at hy'
    have hy'' : y ∈ A ∩ B
    constructor
    · exact hy
    · exact hy'
    rw [h] at hy''
    exact hy''
  · intro h
    ext x
    constructor
    all_goals intro hx
    · cases' hx with hxA hxB
      apply h at hxA
      simp at hxA
      exact hxA hxB
    · by_contra
      exact hx


#check interior_compl
lemma compl_of_closure_is_interior_of_compl
    {X : Type} [T : TopologicalSpace X] (A : Set X) :
    (Closure A)ᶜ = Interior (Aᶜ) := by

  ext x
  constructor
  all_goals intro hx

  · simp at hx
    rw [Closure] at hx

    have hx' : ∃ (V : Set X), Neighbourhood V x ∧ V ∩ A = ∅
    exact Filter.frequently_principal.mp hx --exact?

    cases' hx' with V hV
    cases' hV.left with U hU
    use U
    constructor
    · exact hU.right
    · trans V
      exact hU.left
      rw [← ABdisjoint_iff_AsubsBc]
      exact hV.right

  · simp
    cases' hx with U hU
    by_contra hx
    rw [Closure] at hx
    simp at hx

    specialize hx U (by exact OpenNeighb_is_Neighb U x hU.left)

    cases' hU with hU hU'
    rw [← ABdisjoint_iff_AsubsBc] at hU'
    exact hx hU'


#check isClosed_closure
lemma closure_is_closed {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed (Closure A) := by

  refine { isOpen_compl := ?isOpen_compl } --apply?

  rw [compl_of_closure_is_interior_of_compl]
  exact interior_is_open Aᶜ



#check closure_eq_iff_isClosed
example {X : Type} [T : TopologicalSpace X] (A : Set X) :
    IsClosed A ↔ closure A = A := by
  constructor
  all_goals intro h
  · rw [← compl_compl A, isClosed_compl_iff, ← interior_eq_iff_isOpen, interior_compl] at h
    rw [← compl_compl A, ← h, compl_compl]
    exact closure_closure

  · rw [← compl_compl A, isClosed_compl_iff, ← h]
    rw [← interior_compl]
    exact isOpen_interior


#check closure_empty
lemma closure_of_empty {X : Type} [T : TopologicalSpace X] : Closure (∅ : Set X) = ∅ := by
  simp [Closure]
  ext x
  simp
  use Set.univ
  exact univ_is_Neighb x



def Boundary {X : Type} [TopologicalSpace X] (A : Set X) : Set X :=
    {x : X | ∀ V : Set X, Neighbourhood V x → V ∩ A ≠ ∅ ∧ V ∩ Aᶜ ≠ ∅}

lemma closure_is_set_union_boundary {X : Type} [T : TopologicalSpace X]
    (U : Set X) :
    Closure U = U ∪ Boundary U := by

  ext x
  constructor
  all_goals intro hx

  · rw [Closure] at hx
    simp at *

    have cases : x ∈ U ∨ ¬ (x ∈ U)
    exact Classical.em (x ∈ U)

    cases' cases with case1 case2

    · left
      exact case1

    · right
      intro V hV
      specialize hx V hV
      constructor
      · exact hx
      · by_contra c
        have aux : x ∈ V ∩ Uᶜ
        constructor
        · cases' hV with W hW
          apply hW.left
          exact hW.right.left
        · exact case2
        rw [c] at aux
        exact aux

  · cases' hx with h1 h2
    · apply set_inside_closure
      exact h1
    · intro V hV
      specialize h2 V hV
      exact h2.left

#check SeparatedNhds.disjoint_closure_left
lemma disjointU_V_then_disjointClosureU_V {X : Type}
    [T : TopologicalSpace X] {U V : Set X}
    (hV : IsOpen V) (h : U ∩ V = ∅) :
    Closure U ∩ V = ∅ := by

  ext x
  constructor
  all_goals intro hx

  · cases' hx with hxU hxV
    rw [closure_is_set_union_boundary] at hxU

    cases' hxU with hxU hxU

    · have aux : x ∈ U ∩ V
      · constructor
        exact hxU
        exact hxV
      rw [h] at aux
      exact aux
    · have aux : Neighbourhood V x
      · use V
        constructor
        trivial
        constructor
        exact hxV
        exact hV
      specialize hxU V aux
      cases' hxU with hxU
      rw [Set.inter_comm V U] at hxU
      exact hxU h

  · by_contra
    exact hx
