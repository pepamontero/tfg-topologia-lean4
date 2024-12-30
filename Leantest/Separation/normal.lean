import Leantest.BasicProp.basic
import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.usual
import Leantest.BasicProp.subspaces

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅


#check DiscreteTopo
example {X : Type} (T : TopologicalSpace X)
    (f : X → (Set.Icc 0 1 : Set ℝ)) (hT : T = DiscreteTopo X) :
    ContinuousPepa f := by

  rw [ContinuousPepa]
  intro U hU
  cases' hU with A hA
  sorry

example (f : (Set.Ioo 0 1 : Set ℝ) → (Set.Ioo 0 1: Set ℝ))
    (hf : f x = x) : ContinuousPepa [UsualSpace] [] f := by


  rw [ContinuousPepa]
  intro U hU

  cases' hU with A hA


lemma left_empty_implies_disjoint_open_neighbourhoods
    {X : Type} {T : TopologicalSpace X} (C1 : Set X) (C2 : Set X) (hempty : C1 = ∅) : ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅ := by

  use ∅
  use Set.univ
  constructor
  exact isOpen_empty
  constructor
  exact isOpen_univ
  constructor
  exact Set.subset_empty_iff.mpr hempty
  constructor
  exact fun ⦃a⦄ a ↦ trivial
  exact Set.empty_inter Set.univ


lemma right_empty_implies_disjoint_open_neighbourhoods
    {X : Type} {T : TopologicalSpace X} (C1 : Set X) (C2 : Set X) (hempty : C2 = ∅) : ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅ := by

  use Set.univ
  use ∅
  constructor
  exact isOpen_univ
  constructor
  exact isOpen_empty
  constructor
  exact fun ⦃a⦄ a ↦ trivial
  constructor
  exact Set.subset_empty_iff.mpr hempty
  exact Set.inter_empty Set.univ

lemma ioo_open_in_R (a b : ℝ) :
    UsualTopology.IsOpen ((Set.Ioo a b) : Set ℝ) := by

  rw [UsualTopology]
  intro x hx

  use min (x-a) (b-x)  -- nuestro δ

  constructor
  · -- δ > 0 ?
    simp
    exact hx

  · -- (x - δ, x + δ) ⊆ (a, b) ?

    -- hay que diferenciar cuando δ = x-a y δ = b-x

    have cases : (x - a < b - x) ∨ (x - a ≥ b - x)
    exact lt_or_le (x - a) (b - x)

    cases' cases with case1 case2

    · -- case δ = x-a
      intro y hy

      have hδ :  min (x-a) (b-x) = x-a
      simp
      linarith

      rw [hδ] at hy
      simp at hy
      simp
      constructor
      all_goals linarith

    · -- case δ = b-x
      intro y hy

      have hδ :  min (x-a) (b-x) = b-x
      simp
      linarith

      rw [hδ] at hy
      simp at hy
      simp
      constructor
      all_goals linarith


lemma ico_open_in_Icc01 {Y : Set ℝ}
    {hY : Y = Set.Icc 0 1}
    {R : TopologicalSpace Y}
    {hR : R = TopoSubspace UsualTopology Y}
    (b : ℝ) (hb : 0 < b ∧ b < 1) :
    R.IsOpen ({y | (y : ℝ) ∈ Set.Ico 0 b} : Set Y) := by

  rw [hR] -- usar la topo. del subesp.
  rw [UsualTopology] -- usar la def. de T_u
  use ((Set.Ioo (-1) b) : Set ℝ)
  constructor
  · exact ioo_open_in_R (-1) b
  · ext x
    constructor
    all_goals intro hx
    · simp
      simp at hx
      cases' hx with hx1 hx2
      constructor
      · rw [hY] at hx2
        simp at hx2
        cases' hx2 with hx2 hx3
        constructor
        · linarith
        · simp at hx3
          linarith
      · exact hx2
    · simp
      simp at hx
      cases' hx with hx1 hx2
      constructor
      · rw [hY] at hx2
        simp at hx2
        constructor
        · linarith
        · linarith
      · exact hx2

lemma ioc_open_in_Icc01 {Y : Set ℝ}
    {hY : Y = Set.Icc 0 1}
    {R : TopologicalSpace Y}
    {hR : R = TopoSubspace UsualTopology Y}
    (b : ℝ) (hb2 : 0 < b ∧ b < 1) :
    R.IsOpen ({y | (y : ℝ) ∈ Set.Ioc b 1} : Set Y) := by

  sorry





lemma Urysohn {X : Type} {Y : Set ℝ}
    (T : TopologicalSpace X) {R : TopologicalSpace Y}
    {hY : Y = Set.Icc 0 1}
    {hR : R = TopoSubspace UsualTopology Y} :
    NormalTopoSpace T ↔ ∀ C1 : Set X, ∀ C2 : Set X,
    C1 ≠ ∅ → C2 ≠ ∅ →
    IsClosed C1 → IsClosed C2 →
    C1 ∩ C2 = ∅ →
    ∃ f : X → Y,
    ContinuousPepa f ∧
    f '' C1 = ({0} : Set ℝ) ∧ f '' C2 = ({1} : Set ℝ) := by

  constructor

  · -- →
    intro hT C1 C2 hC1 hC2 hC

    sorry

  · -- ←

    /- DEMO
    1. Queremos ver que `X` es Normal.
    2. Consideramos `C1` y `C2` disjuntos y cerrados.
        Queremos ver que existen `U1` y `U2` abiertos disjuntos conteniendo a `C1` y `C2`.

    3. Para la definición de Espacio Normal no se pide que sean no vacíos,
        pero, si alguno de los dos es vacío, es fácil ver que existen tales abiertos.

    4. Si ambos son no vacíos, podemos aplicar la hipótesis.
        Tomamos la función `f` de la hipótesis.
        Consideramos entonces: `U1 = f⁻¹([0, 1/2))` y `U2 = f⁻¹((1/2, 1])`
          * Trivialmente son disjuntos por serlo `[0, 1/2)` y `(1/2, 1]`
          * `[0, 1/2)` y `(1/2, 1]` son abiertos en `[0, 1]` con la top. usual del subesp.
          * Luego `Ui` son abiertos por ser la preimagen por una función continua de abiertos
    -/

    intro h
    rw [NormalTopoSpace] -- `1`
    intro C1 C2 hC1 hC2 hinter -- `2`

    -- `3`
    have hcases1 : C1 = ∅ ∨ C1 ≠ ∅
    · exact eq_or_ne C1 ∅
    have hcases2 : C2 = ∅ ∨ C2 ≠ ∅
    · exact eq_or_ne C2 ∅

    cases' hcases1 with hcases1 hcases1

    -- si C1 es vacío
    exact left_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases1

    -- si C2 es vacío
    cases' hcases2 with hcases2 hcases2
    exact right_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases2

    -- `4`
    specialize h C1 C2 hcases1 hcases2 hC1 hC2 hinter

    let f := Classical.choose h
    let hf := Classical.choose_spec h

    have fdef : f = Classical.choose h
    rfl

    rw [← fdef] at hf

    let u : Set Y := {y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)}
    let v : Set Y := {y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1}

    use f ⁻¹' u
    use f ⁻¹' v

    constructor

    -- * is `f⁻¹( [0, 1/2) )` Open?

    apply hf.left -- aplicar def. de f continua
    apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · simp
      norm_num

    constructor
    -- * is `f⁻¹( (1/2, 0] )` Open?

    sorry
    constructor
    -- * is `C1 ⊆ U1` ?
    sorry
    constructor
    -- * is `C2 ⊆ U2` ?
    sorry
    -- * is `U1 ∩ U2 = ∅` ?
    sorry
