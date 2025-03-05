import Leantest.BasicProp.basic
import Leantest.BasicProp.open
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.trivial
import Leantest.TopoSpaces.usual
import Leantest.TopoSpaces.point

#check Neighbourhood

open TopologicalSpace

/-
      DEF: HAUSDORFF TOPOLOGICAL SPACE
-/

def Hausdorff {X : Type} (_ : TopologicalSpace X) : Prop :=
    --∀ x : X, ∃ U : Set X, Neighbourhood U x
    ∀ x1 x2 : X, x1 ≠ x2 → ∃ V1 : Set X, ∃ V2 : Set X,
    (V1 ∩ V2 = ∅ ∧ Neighbourhood V1 x1 ∧ Neighbourhood V2 x2)


/-
  Example: Every set with the discrete topology is Hausdorff
-/

example [T : TopologicalSpace X] (hT : T = DiscreteTopo X) : Hausdorff T := by
  intro x1 x2 h
  use {x1}
  use {x2}
  constructor
  · -- {x1} ∩ {x2} = ∅
    exact Set.singleton_inter_eq_empty.mpr h
  · constructor
    · -- {x1} entorno de x1
      use {x1}
      constructor
      trivial
      constructor
      trivial
      rw [hT]
      trivial
    · -- {x2} entorno de x2
      use {x2}
      constructor
      trivial
      constructor
      trivial
      rw [hT]
      trivial


/-
  Example: ℝ with the usual topology is Hausdorff
-/

example [T : TopologicalSpace ℝ] (hT : T = UsualTopology) : Hausdorff T := by
  intro x1 x2 h
  let δ := abs (x1 - x2) / 3
  have hδ : δ = abs (x1 - x2) / 3
  · rfl
  have hδ' : δ > 0
  · rw [hδ]
    simp
    exact sub_ne_zero_of_ne h

  use Set.Ioo (x1 - δ) (x1 + δ)
  use Set.Ioo (x2 - δ) (x2 + δ)

  constructor
  · -- show they are disjoint
    ext y
    constructor
    all_goals intro h
    · --rw [hδ] at h
      simp at h
      cases' h with h1 h2

      have cases : x1 < x2 ∨ x2 < x1
      · exact lt_or_gt_of_ne h

      cases' cases with g1 g2

      · have aux1 : |x1 - x2| = - (x1 - x2)
        · apply abs_of_neg
          linarith
        rw [aux1] at hδ
        rw [hδ] at h1 h2
        simp at h1 h2
        linarith

      · have aux1 : |x1 - x2| = x1 - x2
        · apply abs_of_pos
          linarith
        rw [aux1] at hδ
        rw [hδ] at h1 h2
        linarith

    · by_contra
      exact h

  · -- show they are neighbourhoods
    constructor
    · use Set.Ioo (x1 - δ) (x1 + δ)
      constructor
      · trivial
      · constructor
        · simp
          exact hδ'
        · rw [hT]
          apply ioo_open_in_R (x1 - δ) (x1 + δ)
    · use Set.Ioo (x2 - δ) (x2 + δ)
      constructor
      · trivial
      · constructor
        · simp
          exact hδ'
        · rw [hT]
          apply ioo_open_in_R (x2 - δ) (x2 + δ)



/-
      THEOREM:
  If X is a Hausdorff Space, then all its singletons are closed sets.
-/


theorem Hausdorff_imp_singletones_closed {X : Type} [T : TopologicalSpace X]
    (h : Hausdorff T) : ∀ x : X, IsClosed {x} := by

  intro x
  have h' : IsOpen {x}ᶜ
  · rw [A_open_iff_is_heighbourhood_of_all]
    intro y hy
    have hxy : x ≠ y
    · by_contra c
      rw [c] at hy
      apply hy
      trivial
    specialize h x y hxy
    cases' h with V1 h
    cases' h with V2 h
    cases' h with h h1
    cases' h1 with h1 h2
    cases' h1 with U1 h1
    cases' h2 with U2 h2
    use U2
    constructor
    · simp
      have g1 : x ∈ V1
      · apply h1.left
        exact h1.right.left
      have g2 : x ∉ V2
      · by_contra hx
        have hx' : x ∈ V1 ∩ V2
        · constructor; exact g1; exact hx
        rw [h] at hx'
        exact hx'
      by_contra hx
      apply h2.left at hx
      exact g2 hx
    · exact h2.right


  exact { isOpen_compl := h' }


/-
Example: The Point Topology is not Hausdorff
We show it in two different ways:
  1. Using the definition
  2. Using the previous theorem
-/


-- previous lemma
lemma and_or_not (P Q : Prop) : (P ∨ Q) ∧ ¬ Q → P := by
  intro hP
  cases' hP with h1 h2
  cases' h1 with h h
  exact h
  by_contra
  exact h2 h

-- 1. Using the definition
example [T : TopologicalSpace X] (a : X) (h : ∃ x : X, x ≠ a)
    (hT : T = PointTopology X a) : ¬ Hausdorff T := by
  cases' h with x hx
  by_contra h
  specialize h x a hx
  cases' h with Vx h
  cases' h with Va h
  cases' h with h hx
  cases' hx with hx ha
  cases' hx with Ux hx
  cases' hx with hx1 hx2
  cases' hx2 with hx2 hx3
  have ha1 : a ∈ Ux
  · rw [hT] at hx3
    have aux : Ux ≠ ∅
    · by_contra aux
      rw [aux] at hx2
      exact hx2
    apply and_or_not (a ∈ Ux) (Ux = ∅)
    constructor
    exact hx3
    exact aux
  have ha2 : ¬ a ∈ Ux
  · by_contra
    have c : a ∈ Vx ∩ Va
    · constructor
      · apply hx1
        exact ha1
      · cases' ha with Ua ha
        apply ha.left
        exact ha.right.left
    rw [h] at c
    exact c
  exact ha2 ha1



-- 2. Using the previous theorem
example [T : TopologicalSpace X] (a : X) (hX : ∃ x : X, x ≠ a)
    (hT : T = PointTopology X a) : ¬ Hausdorff T := by
  by_contra h
  apply Hausdorff_imp_singletones_closed at h
  specialize h a

  let U : Set X := {a}
  have hU : U = {a} := by rfl
  rw [← hU] at h

  rw [← compl_compl U] at h
  rw [isClosed_compl_iff] at h
  rw [hT] at h
  cases' h with h1 h2
  · have c : a ∉ Uᶜ
    · rw [hU]
      trivial
    exact c h1
  · cases' hX with x hx
    have c : x ∈ Uᶜ
    · simp
      rw [hU]
      simp
      exact hx
    rw [h2] at c
    exact c
