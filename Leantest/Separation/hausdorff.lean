import Leantest.BasicProp.basic
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

#check Set.Ioo


example {X : Type} [T : TopologicalSpace X]
    (hT : T = DiscreteTopo X) (x : X):
    IsOpen {x} := by
  rw [hT]
  trivial

example (x y: ℝ) : min x y = x ∨ min x y = y := by
  exact min_choice x y

example (x y: ℝ) : x < y ∨ x = y ∨ x > y := by
  exact lt_trichotomy x y

example (x y : ℝ) : x < y → min x y = x := by
  intro h
  exact min_eq_left_of_lt h

example (x y : ℝ) : x = y → min x y = x := by
  intro h
  simp
  exact le_of_eq h


/-
esto habría que meterlo en otro sitio

además, se podría simplificar bastante porque hace dos veces
exáctamente lo mismo y varias veces repite la misma secuencia
de comandos
-/
lemma is_open_open_interval [T : TopologicalSpace ℝ]
    (hT : T = UsualTopology)
    (x y : ℝ) :
    IsOpen (Set.Ioo x y) := by
  rw [hT]
  intro z hz
  let δ := min (z - x) (y - z) / 2
  have hδ : δ = min (z - x) (y - z) / 2 := by rfl
  use δ
  constructor
  · -- δ > 0
    rw [hδ]
    simp
    simp at hz
    exact hz
  · -- let w ∈ (z - δ, z + δ)
    intro w hw
    simp
    have hmin : min (z - x) (y - z) = (z - x) ∨ min (z - x) (y - z) = (y - z)
    · exact min_choice (z - x) (y - z)

    have auxi : z - x < y - z ∨ z - x = y - z ∨ z - x > y - z
    · exact lt_trichotomy (z - x) (y - z)

    constructor
    · -- x < w
      simp at hz
      trans z - δ
      · -- x < z - δ
        cases' auxi with h1 h2
        · -- case: z - x < y - z
          have h' : min (z - x) (y - z) = (z - x)
          · exact min_eq_left_of_lt h1
          rw [h'] at hδ
          rw [hδ]
          linarith
        · cases' h2 with h1 h2
          · -- case z - x = y - z
            have h' : min (z - x) (y - z) = (z - x)
            · rw [h1]
              simp
            rw [h'] at hδ
            rw [hδ]
            linarith
          · -- case z - x > y - z
            have h' : min (z - x) (y - z) = (y - z)
            · exact min_eq_right_of_lt h2
            rw [h'] at hδ
            rw [hδ]
            linarith
      · -- z - δ < w
        exact hw.left
    · -- w < y
      trans z + δ
      · -- w < z + δ
        exact hw.right
      · -- z + δ < y
        cases' auxi with h1 h2
        · -- case z - x < y - z
          have h' : min (z - x) (y - z) = z - x
          · exact min_eq_left_of_lt h1
          rw [h'] at hδ
          rw [hδ]
          linarith
        · cases' h2 with h1 h2
          · -- case z - x = y - z
            have h' : min (z - x) (y - z) = (z - x)
            · rw [h1]
              simp
            rw [h'] at hδ
            rw [hδ]
            linarith
          · -- case z - x > y - z
            have h' : min (z - x) (y - z) = (y - z)
            · exact min_eq_right_of_lt h2
            rw [h'] at hδ
            rw [hδ]
            linarith

example (x : ℝ) (h: x < 0) : |x| = - x := by
  exact abs_of_neg h

example (x y: ℝ) (h : x < y) : |x - y| = - (x - y) := by
  apply abs_of_neg
  linarith

example (x y : ℝ) (h1 : x < y) (h2 : y < x) : False := by
  linarith

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
        · apply is_open_open_interval hT (x1 - δ) (x1 + δ)
    · use Set.Ioo (x2 - δ) (x2 + δ)
      constructor
      · trivial
      · constructor
        · simp
          exact hδ'
        · apply is_open_open_interval hT (x2 - δ) (x2 + δ)

/-
RESULTADO
Si X es un espacio topológico Hausdorff,
entonces todo conjunto unipuntual {x} es cerrado
-/

#check IsClosed

example {X : Type} (A : Set X) (hA : ¬ (∃ a, a ∈ A)) : A = ∅ := by
  exact Set.not_nonempty_iff_eq_empty.mp hA


lemma A_open_iff_is_heighbourhood_of_all
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
    -- classeical choose?
    have h : ∀ a : X, a ∈ A → ∃ Ua : Set X, (Ua ⊆ A ∧ OpenNeighbourhood Ua a)
    · exact h

    have aux : A = ∅ ∨ ¬ (A = ∅)
    exact Classical.em (A = ∅)

    cases' aux with h1 h2

    · -- A is empty
      rw [h1]
      exact isOpen_empty

    · -- A is not empty
      have hA : ∃ a, a ∈ A
      · rw [← Set.not_nonempty_iff_eq_empty] at h2
        simp at h2
        exact h2

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
Ejemplo de topología que no es Hausdorff
La topología del punto para conjuntos de 2 o más elementos
-/

-- usando la definición

lemma and_or_not (P Q : Prop) : (P ∨ Q) ∧ ¬ Q → P := by
  intro hP
  cases' hP with h1 h2
  cases' h1 with h h
  exact h
  by_contra
  exact h2 h

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

#check isClosed_compl_iff
#check compl_compl

-- usando el resultado anterior
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
