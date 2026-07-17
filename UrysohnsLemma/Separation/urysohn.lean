import UrysohnsLemma.Separation.normal
import UrysohnsLemma.MyDefs.sets
import UrysohnsLemma.Continuous.bases
import UrysohnsLemma.Separation.def_k
import UrysohnsLemma.BasicProp.interior

/-
      LEMA DE URYSOHN
-/

-- ANCHOR: Urysohn_sig
lemma Urysohn {X : Type} {Y : Set ℝ}
    (T : TopologicalSpace X)
    [T' : TopologicalSpace ℝ]
    (hT' : T' = UsualTopology)
    {R : TopologicalSpace Y}
    {hY : Y = Set.Icc 0 1}
    {hR : R = TopoSubspace T' Y} :
    NormalSpace X ↔
      ∀ C1 : Set X, ∀ C2 : Set X,
      C1 ≠ ∅ → C2 ≠ ∅ →
      IsClosed C1 → IsClosed C2 →
      Disjoint C1 C2 →
      ∃ f : X → Y,
        Continuous f ∧
        f '' C1 = ({⟨0, by simp [hY]⟩} : Set Y) ∧
        f '' C2 = ({⟨1, by simp [hY]⟩} : Set Y) := by
-- ANCHOR_END: Urysohn_sig

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

-- ANCHOR: Urysohn_reciprocal_intro
    intro h
    rw [normal_space_def] -- `1`
    intro C1 C2 hC1 hC2 hinter -- `2`
-- ANCHOR_END: Urysohn_reciprocal_intro

    -- `3`
    cases' eq_or_ne C1 ∅ with hC1empty hC1nempty

    -- si C1 es vacío
    exact left_empty_implies_disjoint_open_neighbourhoods C1 C2 hC1empty

    -- si C2 es vacío
    cases' eq_or_ne C2 ∅ with hC2empty hC2nempty
    exact right_empty_implies_disjoint_open_neighbourhoods C1 C2 hC2empty

    -- `4`

-- ANCHOR: Urysohn_reciprocal_obtain
    obtain ⟨f, hf, hfC1, hfC2⟩ := h C1 C2 hC1nempty hC2nempty hC1 hC2 hinter
-- ANCHOR_END: Urysohn_reciprocal_obtain

-- ANCHOR: Urysohn_reciprocal_use
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)})
    use f ⁻¹' ({y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1})
-- ANCHOR_END: Urysohn_reciprocal_use

    rw [continuous_def] at hf
    rw [hT'] at hR

    constructor
    -- * is `f⁻¹( [0, 1/2) )` Open?
-- ANCHOR: Urysohn_reciprocal_U1_open
    · apply hf -- aplicar def. de f continua
      apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
      · exact hY
      · exact hR
      · norm_num
-- ANCHOR_END: Urysohn_reciprocal_U1_open

    constructor
    -- * is `f⁻¹( (1/2, 0] )` Open?
    · apply hf -- aplicar def. de f continua
      apply ioc_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
      · exact hY
      · exact hR
      · norm_num

    constructor
    -- * is `C1 ⊆ U1` ?
-- ANCHOR: Urysohn_reciprocal_C1_subset_U1
    · rw [← Set.image_subset_iff, hfC1] -- `{0} ⊆ [0, 1/2)` ?
      simp
-- ANCHOR_END: Urysohn_reciprocal_C1_subset_U1

    constructor
    -- * is `C2 ⊆ U2` ?
    · rw [← Set.image_subset_iff, hfC2] -- `{1} ⊆ (1/2, 1]` ?
      simp; norm_num


    -- * is `U1 ∩ U2 = ∅` ?
-- ANCHOR: Urysohn_reciprocal_disjoint
    · apply Disjoint.preimage
      by_contra c
      apply (not_iff_not.mpr (Set.disjoint_iff_inter_eq_empty)).mp at c
      rw [← ne_eq, ← Set.nonempty_iff_ne_empty] at c
      obtain ⟨x, hxu, hxv⟩ := c
      simp at hxu hxv
      linarith
-- ANCHOR_END: Urysohn_reciprocal_disjoint


-- ANCHOR: Urysohn_forward_intro
  · -- →
    intro hT C1 C2 C1nempty C2nempty C1closed C2closed C1C2disj
-- ANCHOR_END: Urysohn_forward_intro

-- ANCHOR: Urysohn_forward_aux
    have C2c_open : IsOpen C2ᶜ := by exact IsClosed.isOpen_compl
    have hC1C2 : C1 ⊆ C2ᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm C1C2disj))

    rw [characterization_of_normal] at hT
-- ANCHOR_END: Urysohn_forward_aux

-- ANCHOR: Urysohn_forward_let_Gg
    let G := H hT C1 C2
    let g := fun x ↦ k hT C1 C2 x
-- ANCHOR_END: Urysohn_forward_let_Gg

-- ANCHOR: Urysohn_forward_let_f
    let f : X → Y := fun x ↦ ⟨g x, by
      rw [hY]
      exact k_in_01 hT C1 C2 x⟩
-- ANCHOR_END: Urysohn_forward_let_f

-- ANCHOR: Urysohn_forward_use_f
    use f
-- ANCHOR_END: Urysohn_forward_use_f

-- ANCHOR: Urysohn_forward_constructor
    constructor
-- ANCHOR_END: Urysohn_forward_constructor

    /-
            1. CONTINUITY OF f
    -/

-- ANCHOR: Urysohn_continuity_rw
    · rw [@continuousInSubspace_iff_trueForBase
        X ℝ Y T T' R hR f
        {s | ∃ a b : ℝ, s = Set.Ioo a b}
        (by exact BaseOfRealTopo hT')]
-- ANCHOR_END: Urysohn_continuity_rw

-- ANCHOR: Urysohn_continuity_introW
      intro W hW
      obtain ⟨a, b, hW⟩ := hW
-- ANCHOR_END: Urysohn_continuity_introW

-- ANCHOR: Urysohn_continuity_neighbourhood
      rw [A_open_iff_neighbourhood_of_all]
      intro x hx
      rw [Set.mem_preimage, hW] at hx
-- ANCHOR_END: Urysohn_continuity_neighbourhood


      -- paso 1. encontrar p, q racionales con `a < p < f(x) < q < b`

-- ANCHOR: Urysohn_continuity_pq
      obtain ⟨p, hp⟩ := exists_rat_btwn hx.left
      obtain ⟨q, hq⟩ := exists_rat_btwn hx.right
-- ANCHOR_END: Urysohn_continuity_pq

-- ANCHOR: Urysohn_continuity_claims
      have claim1 := k_claim1 hT C1 C2
        C1closed (by exact IsClosed.isOpen_compl)
        (by exact hC1C2)

      have claim2 := k_claim2 hT C1 C2
        C1closed (by exact IsClosed.isOpen_compl)
        (by exact hC1C2)
-- ANCHOR_END: Urysohn_continuity_claims

      -- paso 2.1. probar: `x ∉ closure (U_p)`
-- ANCHOR: Urysohn_continuity_aux1
      have aux1 : x ∉ closure (G p)
      · by_contra c
        apply claim1 p x at c
        linarith
-- ANCHOR_END: Urysohn_continuity_aux1

      -- paso 2.1. probar: `x ∈ U_q`
-- ANCHOR: Urysohn_continuity_aux2
      have aux2 : x ∈ G q
      · by_contra c
        apply claim2 q x at c
        linarith
-- ANCHOR_END: Urysohn_continuity_aux2

      -- paso 3. tomamos el abierto `V = U_q \ closure (U_p)`
-- ANCHOR: Urysohn_continuity_use_U
      use (G q) ∩ (closure (G p))ᶜ

      constructor
-- ANCHOR_END: Urysohn_continuity_use_U

      -- paso 4. probar que `U` es entorno abierto de `x`

        -- 4.1. probar que `U ⊆ f ⁻¹' W`
-- ANCHOR: Urysohn_continuity_use_U_intro_y
      · intro y hy
        rw [hW]
        constructor
-- ANCHOR_END: Urysohn_continuity_use_U_intro_y
-- ANCHOR: Urysohn_continuity_case_a
        · have hy : y ∉ G p
          · by_contra c
            apply subset_closure at c
            exact hy.right c
          apply claim2 p y at hy
          linarith
-- ANCHOR_END: Urysohn_continuity_case_a

-- ANCHOR: Urysohn_continuity_case_b
        · have hy := hy.left
          apply subset_closure at hy
          specialize claim1 q y hy
          linarith
-- ANCHOR_END: Urysohn_continuity_case_b

-- ANCHOR: Urysohn_continuity_constructor2
      constructor
-- ANCHOR_END: Urysohn_continuity_constructor2
-- ANCHOR: Urysohn_continuity_xinV
      · -- probar que `x ∈ V`
        constructor
        · exact aux2
        · exact aux1
-- ANCHOR_END: Urysohn_continuity_xinV
-- ANCHOR: Urysohn_continuity_Vopen
      · -- probar que `V` es abierto
        apply IsOpen.inter
        · exact H_isOpen hT C1 C2 C1closed C2c_open hC1C2 q
        · rw [isOpen_compl_iff]
          exact isClosed_closure
-- ANCHOR_END: Urysohn_continuity_Vopen


    /-
            IMAGE OF f
    -/

-- ANCHOR: Urysohn_image_aux
    have aux : ∀ A : Set X, f '' A = g '' A
    · intro A; ext x; simp [f]
-- ANCHOR_END: Urysohn_image_aux

    rw [← Set.image_val_inj, ← Set.image_val_inj]
    rw [aux C1, aux C2]
    simp
-- ANCHOR: Urysohn_forward_finish
    constructor
    /-
            2. f(C1) = {0}
    -/
    · exact k_in_C1_is_0 hT C1 C2 C1closed C2c_open hC1C2 C1nempty
    /-
            3. f(C2) = {1}
    -/

    · exact k_in_C2_is_1 hT C1 C2 C1closed C2c_open hC1C2 C2nempty
-- ANCHOR_END: Urysohn_forward_finish


/--
Version of Urysohn's Lemma as written in Mathlib, i.e.
`exists_continuous_zero_one_of_isClosed`
-/
theorem Urysohn_Mathlib {X : Type} [T : TopologicalSpace X] [N : NormalSpace X]
    {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t)
    : ∃ f : X → ℝ, Continuous f ∧ Set.EqOn f 0 s ∧ Set.EqOn f 1 t ∧ ∀ x, f x ∈ Set.Icc 0 1 := by

    cases' Classical.em (s = ∅) with s_empty s_nempty

    · let f : X → ℝ := fun x ↦ 1
      use f

      constructor
      · rw [continuous_def]
        intro u hu
        cases' Classical.em (1 ∈ u) with h1u h1u
        · have aux : (f ⁻¹' u) = Set.univ
          · ext x; constructor; all_goals intro hx
            · trivial
            · simp [f]
              use h1u
          rw [aux]
          exact isOpen_univ
        · have aux : (f ⁻¹' u) = ∅
          · ext x; constructor; all_goals intro hx
            · simp [f] at hx
              exact h1u hx
            · by_contra; exact hx
          rw [aux]
          exact isOpen_empty

      constructor

      · intro x hx
        rw [s_empty] at hx
        exfalso
        exact hx

      constructor

      · intro x hx
        simp [f]

      · intro x
        simp [f]

    cases' Classical.em (t = ∅) with t_empty t_nempty

    · let f : X → ℝ := fun x ↦ 0
      use f

      constructor
      · rw [continuous_def]
        intro u hu
        cases' Classical.em (0 ∈ u) with h0u h0u
        · have aux : (f ⁻¹' u) = Set.univ
          · ext x; constructor; all_goals intro hx
            · trivial
            · simp [f]
              use h0u
          rw [aux]
          exact isOpen_univ
        · have aux : (f ⁻¹' u) = ∅
          · ext x; constructor; all_goals intro hx
            · simp [f] at hx
              exact h0u hx
            · by_contra; exact hx
          rw [aux]
          exact isOpen_empty

      constructor

      · intro x hx
        simp [f]

      constructor

      · intro x hx
        rw [t_empty] at hx
        exfalso
        exact hx

      · intro x
        simp [f]

    · have C2c_open : IsOpen tᶜ := by exact IsClosed.isOpen_compl
      have hC1C2 : s ⊆ tᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm hd))


      rw [characterization_of_normal] at N

      let G := H N s t
      let g := fun x ↦ k N s t x

      use g

      constructor

      /-
              1. CONTINUITY OF f
      -/

      · let T' := UsualTopology
        have aux := @BaseOfRealTopo T' (by rfl)
        have aux' := (@continuous_iff_trueForBasics
          X ℝ T UsualTopology
          g
          {s | ∃ a b : ℝ, s = Set.Ioo a b}
          (by exact aux)).mpr

        rw [mathlib_open_eq_my_open]
        apply aux'


        intro W hW
        obtain ⟨a, b, hW⟩ := hW

        rw [A_open_iff_neighbourhood_of_all]
        intro x hx
        rw [Set.mem_preimage, hW] at hx


        -- paso 1. encontrar p, q racionales con `a < p < f(x) < q < b`

        obtain ⟨p, hp⟩ := exists_rat_btwn hx.left
        obtain ⟨q, hq⟩ := exists_rat_btwn hx.right

        have claim1 := k_claim1 N s t
          hs (by exact IsClosed.isOpen_compl)
          (by exact hC1C2)

        have claim2 := k_claim2 N s t
          hs (by exact IsClosed.isOpen_compl)
          (by exact hC1C2)

        -- paso 2.1. probar: `x ∉ closure (U_p)`
        have aux1 : x ∉ closure (G p)
        · by_contra c
          apply claim1 p x at c
          linarith

        -- paso 2.1. probar: `x ∈ U_q`
        have aux2 : x ∈ G q
        · by_contra c
          apply claim2 q x at c
          linarith

        -- paso 3. tomamos el abierto `V = U_q \ closure (U_p)`
        use (G q) ∩ (closure (G p))ᶜ

        constructor

        -- paso 4. probar que `U` es entorno abierto de `x`

          -- 4.1. probar que `U ⊆ f ⁻¹' W`
        · intro y hy
          rw [hW]
          constructor
          · have hy : y ∉ G p
            · by_contra c
              apply subset_closure at c
              exact hy.right c
            apply claim2 p y at hy
            linarith

          · have hy := hy.left
            apply subset_closure at hy
            specialize claim1 q y hy
            linarith

        constructor
        · -- probar que `x ∈ V`
          constructor
          · exact aux2
          · exact aux1
        · -- probar que `V` es abierto
          apply IsOpen.inter
          · exact H_isOpen N s t hs C2c_open hC1C2 q
          · rw [isOpen_compl_iff]
            exact isClosed_closure


      /-
              IMAGE OF f
      -/

      constructor
      /-
              2. f(C1) = {0}
      -/
      · have aux :=  k_in_C1_is_0 N s t hs C2c_open hC1C2 s_nempty
        intro x hx
        simp
        have aux' : k N s t x = 0
        · have : k N s t x ∈ k N s t '' s := by
            use x
          rw [aux] at this
          exact this
        exact aux'
      /-
              3. f(C2) = {1}
      -/
      constructor

      · have aux :=  k_in_C2_is_1 N s t hs C2c_open hC1C2 t_nempty
        intro x hx
        simp
        have aux' : k N s t x = 1
        · have : k N s t x ∈ k N s t '' t := by
            use x
          rw [aux] at this
          exact this
        exact aux'


      · intro x
        exact k_in_01 N s t x
