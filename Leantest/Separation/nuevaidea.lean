import Leantest.Separation.normal

/-
función que numera los racionales en [0, 1]
-/

def Q : Set ℚ := {q : ℚ | 0 ≤ q ∧ q ≤ 1} -- `ℚ ∩ [0, 1]`

lemma Q1 : 1 ∈ Q := by simp [Q]
lemma Q0 : 0 ∈ Q := by simp [Q]

lemma hf : ∃ f : ℕ → Q, (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  sorry

noncomputable def f : ℕ → Q := Classical.choose hf

lemma f_prop : (f.Bijective ∧ f 0 = ⟨1, Q1⟩  ∧ f 1 = ⟨0, Q0⟩) := by
  let hf := Classical.choose_spec hf
  exact hf

example (a b : ℕ) : a = b → f a = f b := by exact fun a_1 ↦ congrArg f a_1

lemma f_in_icc01 : ∀ n : ℕ, ⟨0, Q0⟩ ≤ f n ∧ f n ≤ ⟨1, Q1⟩ := by
  intro n
  constructor
  · exact (f n).property.left -- x.property handles membership, here f n is recognized as an element of Q
  · exact (f n).property.right


/-
definición de las funciones r y s:
dado n ∈ ℕ, r y s devuelven naturales tales que
    f r < f n < f s
y estas son las mejores elecciones de r y s
-/


-- existencia de tal r
lemma exists_r (n : ℕ) (hn : n > 1) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by

  let R : Finset ℕ := (Finset.range n).filter (fun m ↦ f m < f n)
  -- tomamos `R = {m ∈ {0, 1, ..., n-1} | f m < f n}`

  -- vemos que R no es vacío
  have hR : R.Nonempty
  · use 1
    simp [R]
    constructor
    · exact hn
    · have aux : f 1 ≤ f n
      · rw [f_prop.right.right]
        exact (f n).property.left
      have aux' : f 1 ≠ f n
      · by_contra c
        apply (f_prop.left).left at c
        linarith
      exact lt_of_le_of_ne aux aux'

  let fR : Finset Q := R.image f
  -- tomamos el conjunto de as imágenes de R

  -- vemos que no es vacío
  let hfR : fR.Nonempty
  exact (Finset.image_nonempty).mpr hR

  -- tomamos el máximo de las imágenes
  let fr := Finset.max' fR hfR
  have hfr : fr ∈ fR
  exact Finset.max'_mem fR hfR

  -- condición de máximo
  have hfr' : ∀ fm ∈ fR, fm ≤ fr
  exact fun fm a ↦ Finset.le_max' fR fm a
  have hfr' : ∀ m ∈ R, f m ≤ fr
  intro m hm
  have aux : f m ∈ fR
  exact Finset.mem_image_of_mem f hm
  exact hfr' (f m) aux

  -- tomamos el argumento de fr, fr = f r
  have hfr'' : ∃ r ∈ R, f r = fr
  exact Finset.mem_image.mp hfr
  cases' hfr'' with r hr

  use r -- probamos que este r nos vale
  simp [R] at hr

  constructor

  · -- `r ∈ {0, 1, ..., n-1}`?
    simp
    exact hr.left.left

  constructor

  · -- `f r < f n`?
    exact hr.left.right

  · -- si `m ∈ {0, 1, ..., n-1}`, `f m ≤ f r`?
    intro m hm hmn

    have aux : m ∈ R
    simp [R]
    constructor
    · simp at hm
      exact hm
    · exact hmn

    rw [hr.right]
    exact hfr' m aux

-- definición de r y propiedades

noncomputable def r : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_r n h)
  else 0

lemma r_prop (n : ℕ) (hn : n > 1) : (
  (r n ∈ Finset.range n) ∧
  (f (r n) < f n) ∧
  (∀ m ∈ Finset.range n, f m < f n → f m ≤ f (r n))
) := by
  let h := Classical.choose_spec (exists_r n hn)
  simp [r]
  simp [hn]
  simp at h
  exact h



-- existencia de tal s
lemma exists_s (n : ℕ) (hn : n > 1) : ∃ s ∈ Finset.range n,
    ((f n < f s) ∧
    (∀ m ∈ Finset.range n, f n < f m → f s ≤ f m)) := by

  let S : Finset ℕ := (Finset.range n).filter (fun m ↦ f n < f m)
  -- tomamos `S = {m ∈ {0, 1, ..., n-1} | f n < f m}`

  -- vemos que S no es vacío
  have hS : S.Nonempty
  · use 0
    simp [S]
    constructor
    · linarith
    · have aux : f n ≤ f 0
      · rw [f_prop.right.left]
        exact (f n).property.right
      have aux' : f n ≠ f 0
      · by_contra c
        apply (f_prop.left).left at c
        linarith
      exact lt_of_le_of_ne aux aux'

  let fS : Finset Q := S.image f
  -- tomamos el conjunto de as imágenes de S

  -- vemos que no es vacío
  let hfS : fS.Nonempty
  exact (Finset.image_nonempty).mpr hS

  -- tomamos el mínimo de las imágenes
  let fs := Finset.min' fS hfS
  have hfs : fs ∈ fS
  exact Finset.min'_mem fS hfS

  -- condición de mínimo
  have hfs' : ∀ fm ∈ fS, fs ≤ fm
  exact fun fm a ↦ Finset.min'_le fS fm a
  have hfs' : ∀ m ∈ S, fs ≤ f m
  intro m hm
  have aux : f m ∈ fS
  exact Finset.mem_image_of_mem f hm
  exact hfs' (f m) aux

  -- tomamos el argumento de fs, fs = f s
  have hfs'' : ∃ s ∈ S, f s = fs
  exact Finset.mem_image.mp hfs
  cases' hfs'' with s hs

  use s -- probamos que este r nos vale
  simp [S] at hs

  constructor

  · -- `s ∈ {0, 1, ..., n-1}`?
    simp
    exact hs.left.left

  constructor

  · -- `f n < f s`?
    exact hs.left.right

  · -- si `m ∈ {0, 1, ..., n-1}`, `f r ≤ f m`?
    intro m hm hmn

    have aux : m ∈ S
    simp [S]
    constructor
    · simp at hm
      exact hm
    · exact hmn

    rw [hs.right]
    exact hfs' m aux


-- definición de s y propiedades

noncomputable def s : ℕ → ℕ := fun n ↦
  if h : n > 1 then Classical.choose (exists_s n h)
  else 0

lemma s_prop (n : ℕ) (hn : n > 1) : (
  (s n ∈ Finset.range n) ∧
  (f n < f (s n)) ∧
  (∀ m ∈ Finset.range n, f n < f m → f (s n) ≤ f m)
) := by
  let h := Classical.choose_spec (exists_s n hn)
  simp [s]
  simp [hn]
  simp at h
  exact h


/-
RESULTADO PRINCIPAL:
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



noncomputable def Gn {X : Type} [T : TopologicalSpace X]

    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (n : ℕ)
    (hn : n > 1)

    := fun m ↦ (Classical.choose (exists_G hT C1 C2 hC1 hC2 hC1C2 n hn)) m



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

lemma f_has_inverse : ∃ g : Q → ℕ, (
    (∀ n : ℕ, g (f n) = n) ∧
    (∀ q : Q, f (g q) = q)
  ) := by sorry

noncomputable def f_inv : Q → ℕ := Classical.choose f_has_inverse

lemma f_inv_prop : (∀ n : ℕ, f_inv (f n) = n) ∧
    (∀ q : Q, f (f_inv q) = q) := by
  let h := Classical.choose_spec f_has_inverse
  exact h


/-
DEFINICIÓN DE LA G FINAL
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
          simp [f_prop.right.left, f_inv_prop.right]

          sorry

          specialize (H 0 (f_inv ⟨q, hq⟩) (by linarith) (by linarith) (by ))
          rw [h0] at H
          exact H













  sorry
