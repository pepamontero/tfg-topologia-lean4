import Leantest.Separation.normal
import Leantest.MyDefs.my_inf
import Leantest.MyDefs.sets
import Leantest.Continuous.bases
import Leantest.Separation.def_F

/-
      LEMA DE URYSOHN
-/

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
    f '' C1 = ({⟨0, by simp [hY]⟩} : Set Y) ∧ f '' C2 = ({⟨1, by simp [hY]⟩} : Set Y) := by

  constructor
  swap

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
    rw [hT'] at hR
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

    obtain ⟨f, hf⟩ := h C1 C2 hcases1 hcases2 hC1 hC2 hinter

    let U : Set Y := {y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)}
    let V : Set Y := {y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1}

    use f ⁻¹' U
    use f ⁻¹' V

    -- * is `f⁻¹( [0, 1/2) )` Open?
    constructor
    apply hf.left -- aplicar def. de f continua
    apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · norm_num


    -- * is `f⁻¹( (1/2, 0] )` Open?
    constructor
    apply hf.left -- aplicar def. de f continua
    apply ioc_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · norm_num


    -- * is `C1 ⊆ U1` ?
    constructor
    rw [← Set.image_subset_iff, hf.right.left]
    simp
    constructor
    all_goals try norm_num

    -- * is `C2 ⊆ U2` ?

    constructor
    rw [← Set.image_subset_iff, hf.right.right]
    simp
    constructor
    all_goals try norm_num


    -- * is `U1 ∩ U2 = ∅` ?
    by_contra c
    rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at c
    obtain ⟨x, hxu, hxv⟩ := c
    have hxu' := hxu.right
    have hxv' := hxv.left
    linarith




  · -- →
    intro hT C1 C2 hC1 hC2 hC1' hC2' hC1C2

    rw [characterization_of_normal] at hT

    have aux : IsOpen C2ᶜ
    exact IsClosed.isOpen_compl

    have aux' : C1 ⊆ C2ᶜ
    exact ABdisjoint_iff_AsubsBc.mp hC1C2

    let G := H hT C1 C2
    have G_def : G = H hT C1 C2 := by rfl

    -- PROPIEDADES DE G
    have hG := H_Prop hT C1 C2 hC1' aux aux'
    rw [← G_def] at hG
    cases' hG with hG1 hG
    cases' hG with hG0 hG
    cases' hG with hG_open hG_pq

    have hG_empty : ∀ p < 0, G p = ∅
    · intro p hp
      simp [G, H, hp]

    have hG_univ : ∀ p > 1, G p = Set.univ
    · intro p hp
      have aux : ¬ p < 0 := by linarith
      have aux' : ¬ (0 ≤ p ∧ p ≤ 1)
      · simp at aux
        simp [aux]
        linarith
      simp [G, H, aux, aux']

    have aux'' : C1 ⊆ G 0
    · rw [hG0]
      have hG0' := Classical.choose_spec (hT C2ᶜ C1 aux hC1' aux')
      exact hG0'.right.left

    let F := fun x ↦ F hT C1 C2 x

    let k := fun x ↦ k hT C1 C2 x

    have claim1 :  ∀ (p : ℚ), ∀ x ∈ Closure (H hT C1 C2 p), k x ≤ ↑p
    exact fun p x a ↦ claim1 hT C1 C2 hC1' aux aux' p x a

    have claim2 : ∀ (p : ℚ), ∀ x ∉ H hT C1 C2 p, k x ≥ ↑p
    exact fun p x a ↦ claim2 hT C1 C2 hC1' aux aux' p x a



    have k_prop : ∀ x : X, (k x) ∈ Y
    · rw [hY]
      exact fun x ↦ k_in_01 hT C1 C2 x

    let f : X → Y := fun x ↦ ⟨k x, k_prop x⟩
    use f


    constructor

    /-
            1. CONTINUITY OF f
    -/

    · rw [@continuousInSubspace_iff_trueForBase
        X ℝ Y T T' R hR f
        {s | ∃ a b : ℝ, s = Set.Ioo a b}
        (by exact BaseOfRealTopo' hT')]

      intro W hW
      simp at hW
      obtain ⟨a, b, hW⟩ := hW

      rw [characterization_of_open]
      intro x hx
      rw [Set.mem_preimage, hW] at hx


      -- paso 1. encontrar p, q racionales con `a < p < f(x) < q < b`

      have hp : ∃ p : ℚ, a < p ∧ p < Subtype.val (f x)
      exact exists_rat_btwn hx.left
      have hq : ∃ q : ℚ, Subtype.val (f x) < q ∧ q < b
      exact exists_rat_btwn hx.right

      obtain ⟨p, hp⟩ := hp
      obtain ⟨q, hq⟩ := hq


      -- paso 2.1. probar: `x ∉ Closure (G p)`
      have aux1 : x ∉ Closure (G p)
      · by_contra c
        specialize claim1 p x c
        apply not_lt.mpr claim1
        exact hp.right

      -- paso 2.1. probar: `x ∈ G q`
      have aux2 : x ∈ G q
      by_contra c
      specialize claim2 q x c
      apply not_lt.mpr claim2
      exact hq.left

      -- paso 3. tomamos el abierto `V = U_q \ Closure (U_p)`
      use (G q) ∩ (Closure (G p))ᶜ


      constructor

      -- paso 4. probar que `V` es entorno abierto de `x

      · constructor
        · -- probar que `x ∈ V`
          constructor
          · exact aux2
          · exact aux1
        · -- probar que `V` es abierto
          apply IsOpen.inter
          · exact hG_open q
          · rw [isOpen_compl_iff]
            exact closure_is_closed (G p)

      -- paso 5. probar que `f(V) ⊆ U`
      · intro y hy
        simp [hW]
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
        apply hG_empty at hq'
        have hq' : x ∉ G q
        · rw [hq']
          simp
        exact hq' hq

      -- show `{q : ℚ | q ≥ 0} ⊆ F x`
      · simp at hq
        -- two possible cases: either `q > 0` or `q = 0`
        -- in each case we want to see `x ∈ G q`

        have h0 : x ∈ G 0
        · apply aux'' -- apply `C1 ⊆ G 0`
          exact hx

        have hq : q = 0 ∨ q > 0  := by exact Or.symm (LE.le.gt_or_eq hq)
        cases' hq with hq hq

          -- case `q = 0`
        · rw [hq] -- goal here is equivalent by def. to `⊢ x ∈ G 0`
          exact h0

          -- case `q > 0`
        · apply hG_pq 0 q hq
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
            apply hG_pq q 1 hc
            apply set_inside_closure
            exact hq
        rw [hG1] at h1
        exact h1 hx

      · have aux : x ∈ G q
        · rw [hG_univ q hq]
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
