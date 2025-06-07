import Leantest.Separation.normal
import Leantest.MyDefs.sets
import Leantest.Continuous.bases
import Leantest.Separation.def_K
import Leantest.BasicProp.interior

/-
      LEMA DE URYSOHN
-/

#check (inferInstance : TopologicalSpace ℝ)

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
    rw [normal_space_def] -- `1`
    rw [hT'] at hR
    intro C1 C2 hC1 hC2 hinter -- `2`

    -- `3`
    cases' eq_or_ne C1 ∅ with hcases1 hcases1

    -- si C1 es vacío
    exact left_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases1

    -- si C2 es vacío
    cases' eq_or_ne C2 ∅ with hcases2 hcases2
    exact right_empty_implies_disjoint_open_neighbourhoods C1 C2 hcases2

    -- `4`

    obtain ⟨f, hf, hfC1, hfC2⟩ := h C1 C2 hcases1 hcases2 hC1 hC2 hinter
    rw [continuous_def] at hf

    let U : Set Y := {y | (y : ℝ) ∈ Set.Ico 0 (1 / 2)}
    let V : Set Y := {y | (y : ℝ) ∈ Set.Ioc (1 / 2) 1}

    use f ⁻¹' U
    use f ⁻¹' V

    -- * is `f⁻¹( [0, 1/2) )` Open?
    constructor
    apply hf -- aplicar def. de f continua
    apply ico_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · norm_num


    -- * is `f⁻¹( (1/2, 0] )` Open?
    constructor
    apply hf -- aplicar def. de f continua
    apply ioc_open_in_Icc01 -- `[0, 1/2)` es abierto en `[0, 1]`
    · exact hY
    · exact hR
    · norm_num


    -- * is `C1 ⊆ U1` ?
    constructor
    rw [← Set.image_subset_iff, hfC1]
    simp
    constructor
    all_goals try norm_num

    -- * is `C2 ⊆ U2` ?

    constructor
    rw [← Set.image_subset_iff, hfC2]
    simp
    constructor
    all_goals try norm_num


    -- * is `U1 ∩ U2 = ∅` ?
    by_contra c
    rw [Set.disjoint_iff_inter_eq_empty, ← ne_eq, ← Set.nonempty_iff_ne_empty] at c
    obtain ⟨x, hxu, hxv⟩ := c
    have hxu' := hxu.right
    have hxv' := hxv.left
    linarith


  · -- →
    intro hT C1 C2 hC1 hC2 hC1' hC2' hC1C2

    have hC2'' : IsOpen C2ᶜ := by exact IsClosed.isOpen_compl
    have hC1C2' : C1 ⊆ C2ᶜ := by exact Disjoint.subset_compl_left (id (Disjoint.symm hC1C2))

    rw [characterization_of_normal] at hT

    let G := H hT C1 C2

    let g := fun x ↦ k hT C1 C2 x

    let f : X → Y := fun x ↦ ⟨g x, by
      rw [hY]
      exact k_in_01 hT C1 C2 x⟩

    use f

    --- definiciones
    have G_def : G = H hT C1 C2 := by rfl
    have g_def : g = k hT C1 C2 := by rfl

    -- propiedades

    have G_isOpen := H_isOpen hT C1 C2 hC1' hC2'' hC1C2'

    constructor

    /-
            1. CONTINUITY OF f
    -/

    have claim1 := k_claim1 hT C1 C2
      hC1' (by exact IsClosed.isOpen_compl)
      (by exact hC1C2')

    have claim2 := k_claim2 hT C1 C2
      hC1' (by exact IsClosed.isOpen_compl)
      (by exact hC1C2')

    rw [← G_def, ← g_def] at claim1 claim2


    · rw [@continuousInSubspace_iff_trueForBase
        X ℝ Y T T' R hR f
        {s | ∃ a b : ℝ, s = Set.Ioo a b}
        (by exact BaseOfRealTopo' hT')]

      intro W hW
      simp at hW
      obtain ⟨a, b, hW⟩ := hW

      rw [A_open_iff_neighbourhood_of_all]
      intro x hx
      rw [Set.mem_preimage, hW] at hx


      -- paso 1. encontrar p, q racionales con `a < p < f(x) < q < b`

      have hp : ∃ p : ℚ, a < p ∧ p < Subtype.val (f x)
      exact exists_rat_btwn hx.left
      have hq : ∃ q : ℚ, Subtype.val (f x) < q ∧ q < b
      exact exists_rat_btwn hx.right

      obtain ⟨p, hp⟩ := hp
      obtain ⟨q, hq⟩ := hq


      -- paso 2.1. probar: `x ∉ closure (U_p)`
      have aux1 : x ∉ closure (G p)
      · by_contra c
        specialize claim1 p x c
        linarith

      -- paso 2.1. probar: `x ∈ U_q`
      have aux2 : x ∈ G q
      · by_contra c
        specialize claim2 q x c
        linarith

      -- paso 3. tomamos el abierto `V = U_q \ closure (U_p)`
      use (G q) ∩ (closure (G p))ᶜ

      constructor

      -- paso 4. probar que `V` es entorno abierto de `x`

      · intro y hy
        rw [hW]
        constructor
        · have hy : y ∉ G p
          · by_contra c
            apply subset_closure at c
            exact hy.right c
          specialize claim2 p y hy
          linarith

        · have hy := hy.left
          apply subset_closure at hy
          specialize claim1 q y hy
          linarith

      · constructor
        · -- probar que `x ∈ V`
          constructor
          · exact aux2
          · exact aux1
        · -- probar que `V` es abierto
          apply IsOpen.inter
          · exact G_isOpen q
          · rw [isOpen_compl_iff]
            exact isClosed_closure

      -- paso 5. probar que `f(V) ⊆ U`


    /-
            IMAGE OF f
    -/

    have aux : ∀ A : Set X, f '' A = g '' A
    · intro A
      ext x
      simp

    constructor


    /-
            2. f(C1) = {0}
    -/

    apply Set.image_val_inj.mp
    rw [aux C1]
    simp
    rw [g_def]
    exact k_in_C1_is_0' hT C1 C2 hC1' hC2'' hC1C2' hC1


    /-
            3. f(C2) = {1}
    -/

    apply Set.image_val_inj.mp
    rw [aux C2]
    simp
    rw [g_def]
    exact k_in_C2_is_1' hT C1 C2 hC1' hC2'' hC1C2' hC2
