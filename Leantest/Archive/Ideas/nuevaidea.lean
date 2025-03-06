import Leantest.Separation.normal
import Leantest.MyDefs.my_rs_functions


/-
RESULTADO PRINCIPAL:

Sean
  - (X, T) un espacio topológico normal
  - C1, C2 cerrados de X disjuntos

Entonces para cada n > 1, existe una función G_n : ℕ → P(X)
de manera que cumple:
  1. ∀ p ≤ n, G_n(p) es un conjunto abierto
  2. ∀ p, q ≤ n, f p < f q → Closure(G_n(p)) ⊆ G_n(q)
  2. G_n(0) = X \ C2
  3. G_n(1) = V,, C1 ⊆ V ⊆ Closure(V) ⊆ X \ C2
-/


lemma exists_G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)

    :
      ∃ G : ℕ → Set X, (
        (∀ p : ℕ, p ≤ n → IsOpen (G p))
        ∧
        (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
        ∧
        (G 0 = C2ᶜ)
        ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
        )
    := by

  induction' hn with n hn HI

  let h := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)

  · --caso base
    simp
    let G : ℕ → Set X := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
      else Classical.choose (
        hT
          (C2ᶜ)
          (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
          hC2
          (by apply closure_is_closed)
          h.right.right
      )

    let h' := Classical.choose_spec (
      hT
        (C2ᶜ)
        (Closure (Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)))
        hC2
        (by apply closure_is_closed)
        h.right.right
    )

    use G
    constructor

    · -- PROP 1
      intro p hp
      cases' hp with _ hp
      · -- caso p = 2
        simp [G]
        exact h'.left

      cases' hp with _ hp
      · -- caso p = 1
        simp [G]
        exact h.left

      · simp at hp
        simp [hp, G]
        exact { isOpen_compl := hC2 }

    constructor

    · -- PROP 2
      intro p q hp hq hpq

      /-
      NOTA: como f p < f q, y se tiene f 1 ≤ f 2 ≤ f 0,
      los únicos casos posibles son:
      - p = 1, q = 2
      - p = 1, q = 0
      - p = 2, q = 0
      -/

      cases' hp with _ hp

      · -- caso p = 2
        cases' hq with _ hq

        · -- caso q = 2
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f 2)).mp hpq

        cases' hq with _ hq

        · -- caso q = 1
          -- (no puede ser)
          by_contra
          simp at hpq
          rw [f_prop.right.right] at hpq
          exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hpq (f 2).property.left
          -- wow.

        · -- caso q = 0
          simp at hq
          simp [hq, G]
          exact h'.right.right

      cases' hp with _ hp

      · -- caso p = 1

        cases' hq with _ hq

        · -- caso q = 2
          simp [G]
          exact h'.right.left

        cases' hq with _ hq

        · -- caso q = 1
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f 1)).mp hpq

        · -- caso q = 0
          simp at hq
          simp [hq, G]
          exact h.right.right

      · -- caso p = 0
        -- (no puede ser)
        by_contra
        simp at hp
        rw [hp] at hpq
        rw [f_prop.right.left] at hpq
        exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hpq (f q).property.right

    constructor

    · -- PROP 3
      simp [G]

    · -- PROP 4
      simp [G]


  · -- caso recursivo

    simp
    simp at hn
    cases' HI with G' hG'

    let r := r (n + 1)
    let s := s (n + 1)

    have hr : r ≤ n
    apply Nat.le_of_lt_succ
    let aux := (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).left
    simp at aux
    exact aux

    have hs : s ≤ n
    apply Nat.le_of_lt_succ
    let aux := (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).left
    simp at aux
    exact aux

    have hGs : IsOpen (G' s)
    · apply hG'.left
      exact hs

    have hGrs : Closure (G' r) ⊆ G' s
    · apply hG'.right.left
      · exact hr
      · exact hs
      · trans f (n + 1)
        · let aux := (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.left
          exact aux
        · let aux := (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.left
          exact aux

    let G : ℕ → Set X := fun m ↦
      if m < n + 1 then G' m
      else Classical.choose (
        hT
        (G' s)
        (Closure (G' r))
        hGs
        (by apply closure_is_closed)
        hGrs
      )

    let h := Classical.choose_spec (
        hT
        (G' s)
        (Closure (G' r))
        hGs
        (by apply closure_is_closed)
        hGrs
      )

    use G

    constructor

    · -- PROP 1
      intro p hp
      cases' hp with _ hp

      · -- caso p = n + 1
        simp [G]
        exact h.left

      · -- caso p ≤ n
        simp at hp
        rw [← Order.lt_add_one_iff] at hp
        simp [hp, G]
        apply hG'.left
        exact Nat.le_of_lt_succ hp

    constructor

    · -- PROP 2
      intro p q hp hq hpq

      cases' hp with _ hp

      · -- caso p = n+1

        cases' hq with _ hq

        · -- caso q = n+1
          -- (no puede ser)
          by_contra
          exact (lt_self_iff_false (f (n+1))).mp hpq

        · -- caso q ≤ n
          simp at hq
          rw [← Order.lt_add_one_iff] at hq
          simp [hq, G]

          /-
          voy a diferenciar dos casos:
          - q = s
          - q ≠ s
          -/

          have cases : q = s ∨ q ≠ s := by exact eq_or_ne q s
          cases' cases with hqs hqs

          · -- caso q = s
            rw [hqs]
            exact h.right.right

          · -- caso q ≠ s

            trans (G' s)

            · exact h.right.right

            · trans (Closure (G' s))

              · apply set_inside_closure

              · apply hG'.right.left
                · exact hs
                · exact Nat.le_of_lt_succ hq
                · apply lt_of_le_of_ne

                  · simp [s]
                    apply (s_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.right
                    · simp
                      exact hq
                    · exact hpq

                  · by_contra c
                    apply f_prop.left.left at c
                    exact hqs (id (Eq.symm c))

      · -- caso p ≤ n
        simp at hp

        cases' hq with _ hq

        · -- caso q = n+1
          rw [← Order.lt_add_one_iff] at hp
          simp [hp, G]

          /-
          voy a diferenciar dos casos:
          - q = s
          - q ≠ s
          -/

          have cases : p = r ∨ p ≠ r := by exact eq_or_ne p r
          cases' cases with hpr hpr

          · -- caso p = r
            rw [hpr]
            exact h.right.left

          · -- caso p ≠ r

            trans (Closure (G' r))

            · trans (G' r)

              · apply hG'.right.left
                · exact Nat.le_of_lt_succ hp
                · exact hr
                · apply lt_of_le_of_ne

                  · simp [r]
                    apply (r_prop (n+1) (by exact Nat.lt_add_right 1 hn)).right.right
                    · simp
                      exact hp
                    · exact hpq

                  · by_contra c
                    apply f_prop.left.left at c
                    exact hpr c

              · apply set_inside_closure

            · exact h.right.left

        · -- caso q ≤ n
          simp at hq
          rw [← Order.lt_add_one_iff] at hp hq
          simp [hp, hq, G]
          apply hG'.right.left
          · exact Nat.le_of_lt_succ hp
          · exact Nat.le_of_lt_succ hq
          · exact hpq

    constructor

    · -- PROP 3
      simp [G]
      exact hG'.right.right.left

    · -- PROP 4
      have aux : n > 0 := by linarith
      simp [G, aux]
      exact hG'.right.right.right


/-
Def:
  para cada n > 1, definimos G(n) como una elección
  del resultado anterior
-/

noncomputable def Gn {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)

    := fun m ↦ (Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 n hn)) m


/-
Problema: esta elección no me asegura que
  G_n(n) = G_m(n) para n < m
-/

lemma question {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n m : ℕ)
    (hn : n > 1)
    (hm : m > 1)
    (h : n ≤ m)

    :

    (Gn hT C1 C2 hC1 hC2 hC1C2 n hn) n = (Gn hT C1 C2 hC1 hC2 hC1C2 m hm) n := by

  simp [Gn]

  have h1 := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 n hn)
  have h2 := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 m hm)

  sorry


/-
Def: definimos G' : ℕ → P(X) como
  G'(0) = X \ C2
  G'(1) = V,, C1 ⊆ V ⊆ Closure(V) ⊆ X \ C2
  G'(n) = G_n(n)
-/

def G' {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X

    := fun n ↦

  if n = 0 then C2ᶜ
  else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
  else if h : n > 1 then ((Gn hT C1 C2 hC1 hC2 hC1C2 n h) n)
  else ∅

  /-
  La verdad es que no estoy 100% segura de que esta definición vaya a funcionar
  -/

/-
como f es biyectiva, tiene inversa...
-/


/-
Def: definimos la función final que necesitamos, G : ℚ → P(X), como
  G(q) = ∅, si q < 0
  G(q) = G'(f⁻¹(q)), si 0 ≤ q ≤ 1
  G(q) = X, si q > 1
-/

def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : (0 ≤ q ∧ q ≤ 1) then (G' hT C1 C2 hC1 hC2 hC1C2 (f_inv ⟨q, h⟩))
  else Set.univ


/-
CUMPLE LAS PROPIEDADES???
-/

lemma prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p : ℚ, IsOpen (G hT C1 C2 hC1 hC2 hC1C2 p) := by

  intro p

  have cases : p < 0 ∨ 0 ≤ p := by exact lt_or_le p 0
  cases' cases with hp hp

  · -- caso p < 0
    simp [G, hp]

  · -- caso 0 ≤ p
    have cases : p ≤ 1 ∨ 1 < p := by exact le_or_lt p 1
    cases' cases with hp' hp

    · -- caso 0 ≤ p ≤ 1
      have aux : ¬ p < 0
      · linarith
      have hp : 0 ≤ p ∧ p ≤ 1
      · constructor; exact hp; exact hp'

      simp [G, aux, hp]

      cases' (f_inv ⟨p, hp⟩) with k
      · simp [G']
        exact { isOpen_compl := hC2 }

      · cases' k with k
        · simp [G']
          let h := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
          exact h.left

        · simp [G']
          simp [Gn]
          let h := Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (k + 1 + 1) (by linarith))
          let h := h.left
          exact h (k + 1 + 1) (by linarith)

    · -- caso 1 < p
      have aux : ¬ p < 0
      · linarith
      have aux' : ¬ (0 ≤ p ∧ p ≤ 1)
      · simp
        intro
        exact hp
      simp [G, hp, aux, aux']

lemma prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ∀ p q: ℚ, p < q → Closure (G hT C1 C2 hC1 hC2 hC1C2 p) ⊆ G hT C1 C2 hC1 hC2 hC1C2 q := by

  intro p q hpq

  /-
  se divide en varios casos.

  1. si `p < 0`, entonces el goal se traduce a `∅ ⊆ U`,
    que es cierto para todo U

  2.  si `q > 1`, entonces el goal se traduce a `U ⊆ Set.univ`,
    que es cierto para todo U

  3. en caso contrario, si `0 ≤ p` y `q ≤ 1`, puesto que
    `p < q` se tiene `p, q ∈ Q`, luego podemos aplicar
    la inversa de `f` y la definición de `Gn`
  -/

  have cases : q < 0 ∨ 0 ≤ q := by exact lt_or_le q 0
  cases' cases with hq0 hq0

  · -- caso 1. q < 0
    have hp : p < 0 := by linarith
    simp [G, hp, hq0, closure_of_empty]

  have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
  cases' cases with hq1 hq1

  · -- casos 2 y 3. 0 ≤ q ≤ 1
    have cases : p < 0 ∨ 0 ≤ p := by exact lt_or_le p 0
    cases' cases with hp0 hp0

    · -- caso 2. p < 0, q ∈ [0, 1]
      simp [G, hp0, closure_of_empty]

    · -- caso 3. p, q ∈ [0, 1]
      have auxq : ¬ q < 0 := by linarith
      have auxp : ¬ p < 0 := by linarith
      have hq : 0 ≤ q ∧ q ≤ 1 := by simp [hq0, hq1]
      have hp : 0 ≤ p ∧ p ≤ 1 := by simp [hp0]; linarith

      simp [G, auxq, auxp, hq, hp]

      have h : p ≠ q := by linarith
      have h' : f_inv ⟨p, hp⟩ ≠ f_inv ⟨q, hq⟩
      · by_contra c
        apply congrArg f at c
        simp [f_inv_prop.right] at c
        exact h c

      have cases : f_inv ⟨p, hp⟩ = 0 ∨ f_inv ⟨p, hp⟩ > 0 := by exact Nat.eq_zero_or_pos (f_inv ⟨p, hp⟩)
      cases' cases with hfp hfp

      · -- caso 3.1. f⁻¹(p) = 0
        have cases : f_inv ⟨q, hq⟩ = 0 ∨ f_inv ⟨q, hq⟩ > 0 := by exact Nat.eq_zero_or_pos (f_inv ⟨q, hq⟩)
        cases' cases with hfq hfq

        · -- caso 3.1.1. f⁻¹(q) = 0
          -- imposible porque f⁻¹(p) ≠ f⁻¹(q)
          simp [hfp, hfq] at h'

        have cases : f_inv ⟨q, hq⟩ = 1 ∨ f_inv ⟨q, hq⟩ > 1 := by exact LE.le.eq_or_gt hfq
        cases' cases with hfq hfq

        · -- caso 3.1.2. f⁻¹(q) = 1
          have auxp : p = 1
          · apply congrArg f at hfp
            simp [f_prop.right.left, f_inv_prop.right] at hfp
            have h_proj := Subtype.mk.inj hfp
            -- no entiendo muy bien esto
            exact h_proj

          have auxq : q = 0
          · apply congrArg f at hfq
            simp [f_prop.right.right, f_inv_prop.right] at hfq
            have h_proj := Subtype.mk.inj hfq
            exact h_proj

          by_contra
          simp [auxp, auxq] at hpq
          linarith

        · -- caso 2.1.3. f⁻¹(q) > 1
          have auxq : ¬ f_inv ⟨q, hq⟩ = 0 := by linarith
          have auxq' : ¬ f_inv ⟨q, hq⟩ = 1 := by linarith
          simp [hfp, hfq, auxq, auxq', G']
          simp [Gn]
          have h := (Classical.choose_spec (exists_G hT C1 C2 hC1 hC2 hC1C2 (f_inv ⟨q, hq⟩) hfq))
          have H := h.right.left
          have h0 := h.right.right

          have aux : f 0 < f (f_inv ⟨q, hq⟩)
          · simp [f_prop.right.left, f_inv_prop.right]
            sorry
          sorry

      · sorry
  sorry


def propG {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)
    (G : ℕ → Set X) : Prop :=

    (
      (G 0 = C2ᶜ) ∧
      (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)) ∧
      (∀ p ≤ n, IsOpen (G p)) ∧
      (∀ p ≤ n, ∀ q ≤ n, f p < f q → Closure (G p) ⊆ G q) ∧
      ((h : n - 1 > 1) →
        (∀ G' : ℕ → Set X, (propG hT C1 C2 hC1 hC2 hC1C2 (n-1) h G') →
          (∀ m < n, G m = G' m)
        )
      )
    )
