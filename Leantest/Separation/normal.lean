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
  intro ε hε
  sorry


lemma ico_open_in_Icc01 {Y : Set ℝ}
    {hY : Y = Set.Icc 0 1}
    (b : ℝ) (hb : 0 < b ∧ b < 1) :
    (TopoSubspace UsualTopology Y).IsOpen
      ((fun y => (y : ℝ) ∈ Set.Ico 0 b) : Set Y) := by

  -- use U = [0, b) = (-1, b) ∩ [0, 1] = V ∩ Y
  let V : Set ℝ := Set.Ioo (-1) b
  have Vdef : V = Set.Ioo (-1) b
  rfl
  use V
  constructor
  rw [Vdef]

  -- show V is open
  exact ioo_open_in_R (-1) b

  -- show U = V ∩ Y
  ext x
  constructor
  · simp
    intro hx hx'
    constructor
    · rw [Vdef]
      simp
      constructor
      · rw [hY] at hx
        simp at hx
        linarith
      · exact hx'.right
    · exact hx

  · intro hx
    simp
    cases' hx with hx hx'
    use hx'
    constructor
    · rw [hY] at hx'
      simp at hx'
      exact hx'.left
    · rw [Vdef] at hx
      simp at hx
      exact hx.right

lemma idk {X : Type} {Y : Set X}
    {TX : TopologicalSpace X}
    {TY : TopologicalSpace Y}
    {hT : TY = TopoSubspace TX Y}
    (u : Set X) (hu : TX.IsOpen u)
    {v : Set Y}
    {hv : v = fun y => (y : Y) ∈ u} :
    TY.IsOpen := by
  sorry



lemma Uryshon {X : Type} {Y : Set ℝ}
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
    Queremos ver que `X` es Normal.
    Consideramos `C1` y `C2` disjuntos y cerrados.
    Queremos ver que existen `U1` y `U2` abiertos disjuntos conteniendo a `C1` y `C2`.

    Para la definición de Espacio Normal no se pide que sean no vacíos,
    pero, si alguno de los dos es vacío, es fácil ver que existen tales abiertos.

    Si ambos son no vacíos, podemos aplicar la hipótesis.
    Tomamos la función `f` de la hipótesis.
    Consideramos entonces: `U1 = f⁻¹([0, 1/2))` y `U2 = f⁻¹((1/2, 1])`
      * Trivialmente son disjuntos por serlo `[0, 1/2)` y `(1/2, 1]`
      * `[0, 1/2)` y `(1/2, 1]` son abiertos en `[0, 1]` con la top. usual del subesp.
      * Luego `Ui` son abiertos por ser la preimagen por una función continua de abiertos
    -/

    intro h
    rw [NormalTopoSpace]
    intro C1 C2 hC1 hC2 hinter

    have hcases1 : C1 = ∅ ∨ C1 ≠ ∅
    · exact eq_or_ne C1 ∅
    have hcases2 : C2 = ∅ ∨ C2 ≠ ∅
    · exact eq_or_ne C2 ∅

    cases' hcases1 with hcases1 hcases1
    -- CASOS

    -- si C1 es vacío
    exact left_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases1

    -- si C2 es vacío
    cases' hcases2 with hcases2 hcases2
    exact right_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases2

    -- ambos son no vacíos (aplicamos hipótesis)
    specialize h C1 C2 hcases1 hcases2 hC1 hC2 hinter

    let f := Classical.choose h
    let hf := Classical.choose_spec h

    have fdef : f = Classical.choose h
    rfl

    rw [← fdef] at hf

    let u : Set ℝ := Set.Ico 0 (1/2)
    let u_Y : Set Y := fun y => (y : ℝ) ∈ u

    let v : Set ℝ := Set.Ioc (1/2) 0
    let v_Y : Set Y := fun y => (y : ℝ) ∈ v

    use f ⁻¹' u_Y
    use f ⁻¹' v_Y

    constructor

    -- 1
    -- is `f⁻¹( [0, 1/2) )` Open?
    -- by the definition of continuous
    apply hf.left
    -- is `[0, 1/2)` Open in Y?
    rw [hR]
    rw [UsualTopology]
    use ((Set.Ioo (-1) (1/2)) : Set ℝ)
    constructor
    · exact ioo_open_in_R (-1) (1/2)
    · ext x
      constructor
      · intro hx
        simp at hx
        simp
        cases' hx with hx1 hx2
        constructor
        rw [u_Y] at hx2
        sorry
        exact hx1





    exact ico_open_in_Icc01 (1/2)
    constructor
    -- `f⁻¹( (1/2, 0] )` is Open?
    sorry
    constructor
    sorry
    constructor
    sorry



    sorry
