import Leantest.BasicProp.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.trivial
import Leantest.TopoSpaces.usual

#check Neighbourhood

open TopologicalSpace

example [TopologicalSpace ℝ] : Neighbourhood (Set.Icc 1 3) 2 := by
  rw [Neighbourhood]
  use Set.Icc 1 3
  constructor
  simp
  rw [OpenNeighbourhood]
  constructor
  trivial
  trivial

def Hausdorff {X : Type} (T : TopologicalSpace X) : Prop :=
    --∀ x : X, ∃ U : Set X, Neighbourhood U x
    ∀ x1 x2 : X, x1 ≠ x2 → ∃ V1 : Set X, ∃ V2 : Set X,
    (V1 ∩ V2 = ∅ ∧ Neighbourhood V1 x1 ∧ Neighbourhood V2 x2)


example (X : Type) (x a : X) (h : a ∈ Set.singleton x) : a = x := by
  exact h

#check Set.singleton_inter_eq_empty.mpr
example (X : Type ) (x y : X) (h : x ≠ y) : Set.singleton x ∩ Set.singleton y = ∅ := by
  ext a
  constructor <;> intro h'
  simp at h'
  have h1 : a = x
  exact h'.left
  have h2 : a = y
  exact h'.right
  rw [← h1, ← h2] at h
  dsimp at h
  apply h
  trivial
  by_contra
  exact h'


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
    (x y : ℝ) (h : x < y) :
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
          linarith
    · use Set.Ioo (x2 - δ) (x2 + δ)
      constructor
      · trivial
      · constructor
        · simp
          exact hδ'
        · apply is_open_open_interval hT (x2 - δ) (x2 + δ)
          linarith
