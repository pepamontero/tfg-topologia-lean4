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



/-
                 LEMA DE URYSOHN
-/


lemma existence_of_opens_for_urysohn {X : Type}
    (T : TopologicalSpace X)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2) :
    ∃ G : ℚ → Set X, (∀ p : ℚ, IsOpen (G p)) ∧
    (∀ p q : ℚ, p < q → Closure (G p) ⊆ G q) := by

  let Gneg : ℚ → Set X := fun q : ℚ ↦ (∅ : Set X)
  let Gpos : ℚ → Set X := fun q : ℚ ↦ Set.univ

  let G0 : ℚ → Set X := fun q : ℚ ↦ Set.univ

  let f : ℕ → ℚ

  let G : ℚ → Set X

  let P : Finset ℕ := {}
  let k : ℕ := Finset.card P

  sorry
  sorry
  sorry


lemma Urysohn {X : Type} {Y : Set ℝ}
    (T : TopologicalSpace X)
    [T' : TopologicalSpace ℝ]
    (hT' : T' = UsualTopology)
    {R : TopologicalSpace Y}
    {hY : Y = Set.Icc 0 1}
    {hR : R = TopoSubspace T' Y} :
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

    have H : ∃ G : ℚ → Set X, (∀ p : ℚ, IsOpen (G p)) ∧
    (∀ p q : ℚ, p < q → Closure (G p) ⊆ G q)
    sorry

    have aux : IsOpen C2ᶜ
    exact IsClosed.isOpen_compl

    have aux' : C1 ⊆ C2ᶜ
    exact ABdisjoint_iff_AsubsBc.mp hC1C2

    /-


    let g : Q → Set X := fun p =>
      match p with
      | ⟨1, trivial⟩ => C2ᶜ
      | ⟨0, trivial⟩ => Classical.choose (h C2ᶜ C1 aux hC1' aux')
      | q => ∅


    let a : Q × Set Q → Prop := fun (q, P) ↦ (Set.Mem P q)


    let g_rec : Q × Set Q → Set X := fun (q, P) =>
      let D : Prop := ∃ p ∈ P, p = q
      if D then g q


    -/


    -- setting up G
    let G : ℚ → Set X := Classical.choose H
    let hG := Classical.choose_spec H
    cases' hG with hG1 hG2
    have Gdef : G = Classical.choose H := by rfl
    rw [← Gdef] at hG1 hG2

    -- COSAS QUE VOY NECESITANDO SOBRE G
    -- (que deberían ser ciertas por construcción de G)
    have hG3 : G 0 = Classical.choose (h C2ᶜ C1 aux hC1' aux')
    sorry

    let hG3' := Classical.choose_spec (h C2ᶜ C1 aux hC1' aux')
    rw [← hG3] at hG3'

    have hG4 : G 1 = C2ᶜ
    sorry

    have hG5 : ∀ p < 0, G p = ∅
    sorry

    have hG6 : ∀ p > 1, G p = Set.univ
    sorry


    -- setting up F
    let F : X → Set ℚ := fun x : X ↦ {p : ℚ | x ∈ G p}

    have hF1 : ∀ x : X, F x ≠ ∅
    sorry

    have hF2 : ∀ x : X, ∀ p ∈ F x, 0 ≤ p ∧ p ≤ 1
    sorry

    have hF3 : ∀ x : X, hasMyInf (F x)
    sorry

    -- setting up f
    let k : X → ℝ := fun x ↦ MyInf (F x) (hF3 x)
    have hk : ∀ x : X, (k x) ∈ Y
    sorry

        -- CLAIMS
    have claim1 : ∀ p : ℚ, ∀ x : X, x ∈ Closure (G p) → (k x) ≤ p
    sorry

    have claim2 : ∀ p : ℚ, ∀ x : X, x ∉ (G p) → (k x) ≥ p
    sorry

    let f : X → Y := fun x ↦ ⟨k x, hk x⟩
    use f




    constructor

    /-
            1. CONTINUITY OF f
    -/

    · let fB : ℝ × ℝ → Set ℝ := fun (a, b) ↦ Set.Ioo a b
      have hfB : ∀ a b : ℝ, fB (a, b) = Set.Ioo a b
      exact fun a b ↦ rfl
      let B : (Set (Set ℝ)) := fB '' (Set.univ)
      have B_def : B = fB '' (Set.univ) := by rfl
      have hB : isTopoBase B := by exact BaseOfRealTopo hT' fB hfB

      rw [@continuousInSubspace_iff_trueForBase X ℝ Y T T' R hR f B hB]

      intro W hW
      rw [characterization_of_open]
      intro x hx

      simp at hx


      have basicW : ∃ a b : ℝ, W = {x : ℝ | a < x ∧ x < b}
      · rw [B_def] at hW
        simp at hW
        cases' hW with a hW
        cases' hW with b hW
        use a
        use b
        rw [← hW]
        exact hfB a b

      cases' basicW with a basicW
      cases' basicW with b basicW

      simp [basicW] at hx


      -- paso 1. encontrar p, q racionales con `a < p < f(x) < q < b`
      have hp : ∃ p : ℚ, a < p ∧ p < k x
      exact exists_rat_btwn hx.left
      have hq : ∃ q : ℚ, k x < q ∧ q < b
      exact exists_rat_btwn hx.right

      cases' hp with p hp
      cases' hq with q hq

      -- paso 2.1. probar: `x ∉ Closure (G p)`
      have yanose1 : x ∉ Closure (G p)
      by_contra c
      specialize claim1 p x c
      apply not_lt.mpr claim1
      exact hp.right

      -- paso 2.1. probar: `x ∈ G q`
      have yanose2 : x ∈ G q
      by_contra c
      specialize claim2 q x c
      apply not_lt.mpr claim2
      exact hq.left

      -- paso 3. tomamos el abierto `V = U_q \ Adh(U_p)`
      use (G q) ∩ (Closure (G p))ᶜ


      constructor

      -- paso 4. probar que `V` es entorno abierto de `x

      · constructor
        · -- probar que `x ∈ V`
          constructor
          · exact yanose2
          · exact yanose1
        · -- probar que `V` es abierto
          apply IsOpen.inter
          · exact hG1 q
          · rw [isOpen_compl_iff]
            exact closure_is_closed (G p) --exact? looks for my lemma

      -- paso 5. probar que `f(V) ⊆ U`
      · intro y hy
        simp [basicW]
        constructor
        · cases' hy with _ hy
          have hy : y ∉ G p
          · by_contra c
            apply set_inside_closure at c
            exact hy c
          specialize claim2 p y hy
          linarith

        · cases' hy with hy _
          apply set_inside_closure at hy
          specialize claim1 q y hy
          linarith

    constructor


    /-
            2. f(C1) = {0}
    -/

    -- paso 1. ver que, si `x ∈ C1`, entonces `F x = {q : q ≥ 0}`

    have hFC1 : ∀ x ∈ C1, F x = {q : ℚ | q ≥ 0}
    · intro x hx
      ext q
      constructor
      all_goals intro hq

      -- show `F x ⊆ {q : ℚ | q ≥ 0}`
      -- use: if `q < 0` then `U q = ∅`
      · simp
        by_contra hq'
        simp at hq'
        apply hG5 at hq'
        have hq' : x ∉ G q
        · rw [hq']
          simp
        exact hq' hq

      -- show `{q : ℚ | q ≥ 0} ⊆ F x`
      · simp at hq
        -- two possible cases: either `q > 0` or `q = 0`
        -- in each case we want to see `x ∈ G q`

        have h0 : x ∈ G 0
        · apply hG3'.right.left -- apply `C1 ⊆ G 0`
          exact hx

        have hq : q = 0 ∨ q > 0  := by exact Or.symm (LE.le.gt_or_eq hq)
        cases' hq with hq hq

          -- case `q = 0`
        · rw [hq] -- goal here is equivalent by def. to `⊢ x ∈ G 0`
          exact h0

          -- case `q > 0`
        · specialize hG2 0 q hq
          apply hG2
          apply set_inside_closure
          exact h0

    -- paso 2. ver que 0 es ínfimo de F x
    have hF0 :  ∀ x ∈ C1, isMyInf 0 (F x)
    · intro x hx
      specialize hFC1 x hx
      constructor
      · intro p hp
        simp [hFC1] at hp
        simp
        exact hp
      · intro y hy
        specialize hy 0
        simp [hFC1] at hy
        exact hy

    have hFInf : ∀ x ∈ C1, hasMyInf (F x)
    · intro x hx
      use 0
      exact hF0 x hx

    -- paso 3. ver que k x = 0
    have hkC1 : ∀ x ∈ C1, k x = 0
    · intro x hx
      specialize hFInf x hx
      specialize hF0 x hx

      let hspec := Classical.choose_spec hFInf
      exact inf_is_unique (Classical.choose hFInf) 0 (F x) hspec hF0


    -- paso 4. DEMO `f(C1) = {0}`

    ext r
    constructor
    · simp
      intro x hx hkx
      rw [← hkx]
      exact hkC1 x hx
    · simp
      intro hr
      rw [hr]
      apply nonempty_has_element at hC1
      cases' hC1 with x hx
      use x
      constructor
      · exact hx
      · exact hkC1 x hx

    /-
            3. f(C2) = {1}
    -/

    -- paso 1. ver que, si `x ∈ C1`, entonces `F x = {q : q ≥ 0}`

    have hFC2 : ∀ x ∈ C2, F x = {q : ℚ | q > 1}
    · intro x hx
      ext q
      simp
      constructor
      all_goals intro hq

      · by_contra hc
        simp at hc

        -- let's show that if `q ≤ 1`, then `x ∈ G 1`
        -- which is a contradiction since `G 1 = C2ᶜ`
        have h1 : x ∈ G 1
        · have hc : q = 1 ∨ q < 1 := by exact Or.symm (Decidable.lt_or_eq_of_le hc)
          cases' hc with hc hc
          · -- if `q = 1`, by definition of F
            rw [hc] at hq
            exact hq
          · -- if `q < 1`, by property of G (hG2)
            specialize hG2 q 1 hc
            apply hG2
            apply set_inside_closure
            exact hq
        rw [hG4] at h1
        exact h1 hx

      · specialize hG6 q hq
        have aux : x ∈ G q
        · rw [hG6]
          trivial
        exact aux

    -- paso 2. ver que 1 es ínfimo de F x
    have hF1 :  ∀ x ∈ C2, isMyInf 1 (F x)
    · intro x hx
      specialize hFC2 x hx
      constructor
      · intro p hp
        rw [hFC2] at hp
        simp at hp
        have hp : 1 ≤ p
        · exact le_of_lt hp
        exact_mod_cast hp -- exact_mod_cast deals with coercions
      · intro y hy
        rw [isMyLowerBound] at hy
        by_contra hc
        simp at hc
        have hq : ∃ q : ℚ, 1 < q ∧ q < y
        · exact_mod_cast exists_rat_btwn hc
        cases' hq with q hq
        cases' hq with hq1 hq2
        have hq' : q ∈ F x
        · simp [hFC2]
          exact hq1
        specialize hy q hq'
        linarith

    have hFInf : ∀ x ∈ C2, hasMyInf (F x)
    · intro x hx
      use 1
      exact hF1 x hx

    -- paso 3. ver que k x = 1
    have hkC1 : ∀ x ∈ C2, k x = 1
    · intro x hx
      specialize hFInf x hx
      specialize hF1 x hx

      let hspec := Classical.choose_spec hFInf
      exact inf_is_unique (Classical.choose hFInf) 1 (F x) hspec hF1


    -- paso 4. DEMO `f(C2) = {1}`

    ext r
    constructor
    · simp
      intro x hx hkx
      rw [← hkx]
      exact hkC1 x hx
    · simp
      intro hr
      rw [hr]
      apply nonempty_has_element at hC2
      cases' hC2 with x hx
      use x
      constructor
      · exact hx
      · exact hkC1 x hx




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
    · rw [hT'] at hR
      exact hR
    · simp
      norm_num


    -- * is `f⁻¹( (1/2, 0] )` Open?
    constructor
    apply hf.left -- aplicar def. de f continua
    apply ioc_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · rw [hT'] at hR
      exact hR
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
