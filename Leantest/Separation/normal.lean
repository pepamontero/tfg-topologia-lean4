import Leantest.BasicProp.basic
import Leantest.Continuous.basic
import Leantest.TopoSpaces.discrete
import Leantest.TopoSpaces.usual
import Leantest.BasicProp.subspaces
import Leantest.BasicProp.closure

set_option diagnostics true
set_option diagnostics.threshold 1500


/-
      DEF: ESPACIO NORMAL
-/

def NormalTopoSpace {X : Type} (T : TopologicalSpace X) : Prop :=
    ∀ C1 : Set X, ∀ C2 : Set X,
    IsClosed C1 → IsClosed C2 → C1 ∩ C2 = ∅ →
    ∃ U1 : Set X, ∃ U2 : Set X, IsOpen U1 ∧ IsOpen U2 ∧
    C1 ⊆ U1 ∧ C2 ⊆ U2 ∧ U1 ∩ U2 = ∅


/-
            RESULTADOS SOBRE ABIERTOS
      [hay que moverlo a otro archivo]
-/


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

  rw [hR] -- usar la topo. del subesp.
  rw [UsualTopology] -- usar la def. de T_u
  use ((Set.Ioo b 2) : Set ℝ)
  constructor
  · exact ioo_open_in_R b 2
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

/-
    fin resultados sobre abiertos [necesario mover]
-/



/-
          CARACTERIZACIÓN DE NORMAL
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


/-                    INTENTOS PARA LA SUCESIÓN

example {X : Type} (T : TopologicalSpace X)
    (hT : NormalTopoSpace T) (Q : Set ℝ)
    (hQ : Q = {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x} ):
    ∃ (f : Q → Set X),
    ∀ (p q : Q), p < q →
    Closure (f p) ⊆ f q := by



  sorry

example {X : Type} (T : TopologicalSpace X)
    (hT : NormalTopoSpace T) (Q : Set ℝ)
    (hQ : Q = {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ q : ℚ, (q : ℝ) = x} ) :
    ∀ (p q : Q), p< q → ∃ Up Uq : Set X,
    IsOpen Up ∧ IsOpen Uq ∧ Closure (Up) ⊆ Uq := by

  intro p q hpq

  rw [hQ] at p
  simp at p
  cases' p with p hp
  cases' hp with hp1 hp3
  cases' hp1 with hp1 hp2


  sorry

example {X : Type} (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (p q : ℚ)
    (hp1 : p ≥ 0) (hp2 : p ≤ 1)
    (hq1 : q ≥ 0) (hq2 : q ≤ 1)
    (hpq : p < q) :
    ∃ Up Uq : Set X,
    IsOpen Up ∧ IsOpen Uq ∧ Closure (Up) ⊆ Uq := by


  sorry


/- QUIERO INTENTAR ALGO ASI:
def f : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n+2) => f n + f (n+1)

#eval f 5

example : f 5 = 5 := by
  repeat rw [f]
-/

def thissucc {X : Type} [T : TopologicalSpace X]
    (hT : NormalTopoSpace T) (Q : Set ℚ)
    (hQ : Q = {x : ℚ | 0 ≤ x ∧ x ≥ 1})
    : Q → Set X :=

    sorry

-/



/-
                 LEMA DE URYSOHN
-/



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
    intro hT C1 C2 hC1 hC2 hC1' hC2' hC1C2

    have h : ∀ U : Set X, ∀ C : Set X,
    IsOpen U → IsClosed C → C ⊆ U →
    ∃ V : Set X, IsOpen V ∧
    C ⊆ V ∧ (Closure V) ⊆ U
    · rw [characterization_of_normal] at hT
      exact hT

    let Q : Set ℚ := {x : ℚ | 0 ≤ x ∧ x ≥ 1}

    have aux : IsOpen C2ᶜ
    exact IsClosed.isOpen_compl

    have aux' : C1 ⊆ C2ᶜ
    exact ABdisjoint_iff_AsubsBc.mp hC1C2

    let g : Q → Set X := fun p =>
      match p with
      | ⟨1, trivial⟩ => C2ᶜ
      | ⟨0, trivial⟩ => Classical.choose (h C2ᶜ C1 aux hC1' aux')
      | q => ∅

    let g_rec : ℚ → Set ℚ → Set X := fun q P =>
      if Classical.propDecidable (q ∈ P) then g q


    have hf1 : ∀ q : Q, IsOpen (f q)
    sorry

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

    -- * is `f⁻¹( [0, 1/2) )` Open?
    constructor
    apply hf.left -- aplicar def. de f continua
    apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · simp
      norm_num


    -- * is `f⁻¹( (1/2, 0] )` Open?
    constructor
    apply hf.left -- aplicar def. de f continua
    apply ioc_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · simp
      norm_num


    -- * is `C1 ⊆ U1` ?
    constructor
    intro x hx
    simp

    have aux : Subtype.val (f x) ∈ Subtype.val '' (f '' C1)
    · simp
      use x

    rw [hf.right.left] at aux

    have aux': Subtype.val (f x) = 0
    trivial

    constructor
    rw [aux']
    rw [aux']
    norm_num

    -- NOTA . PROBABLEMENTE SE PUEDE SINTETIZAR


    -- * is `C2 ⊆ U2` ?
    constructor
    intro x hx
    simp

    have aux : Subtype.val (f x) ∈ Subtype.val '' (f '' C2)
    · simp
      use x

    rw [hf.right.right] at aux

    have aux': Subtype.val (f x) = 1
    trivial

    constructor
    rw [aux']
    norm_num
    rw [aux']


    -- * is `U1 ∩ U2 = ∅` ?
    ext x
    constructor
    all_goals intro hx

    · simp at hx
      cases' hx with hxu hxv
      cases' hxu with hxu1 hxu2
      cases' hxv with hxv1 hxv2
      linarith

    · by_contra
      exact hx
