import Leantest.Separation.normal
import Leantest.MyDefs.my_rs_functions
import Leantest.MyDefs.my_lex_order
import Leantest.MyDefs.my_induction


#check characterization_of_normal


/-    DEFINICIONES PREVIAS

* `normal_pair`: (U, C) is Normal Pair iff
  U is Open in X, C is Closed in X and C ⊆ U

* `from_normality`
  input: U, C ⊆ X
  output:
  - return V from the characterization of normal
    applied to U and C if (U, C) is a Normal Pair
  - else, return ∅


let (U, C) a Pair. Let V = from_normality (U, C)

* `from_normality_prop1`
  if (U, C) is a Normal Pair, then
  V is Open

* `from_normality_prop2`
  if (U, C) is a Normal Pair, then
  C ⊆ V ⊆ closure V ⊆ U
-/

def normal_pair {X : Type} [TopologicalSpace X]
    : (Set X × Set X) → Prop := fun (U, C) ↦ (IsOpen U ∧ IsClosed C ∧ C ⊆ U)

noncomputable def from_normality {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    : (Set X × Set X) → Set X :=

    fun (U, C) ↦

    if h : normal_pair (U, C) = True then
      Classical.choose (hT
        U
        C
        (by simp at h; exact h.left)
        (by simp at h; exact h.right.left)
        (by simp at h; exact h.right.right)
      )

    else ∅


lemma from_normality_prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (U C : Set X)
    :
    normal_pair (U, C) → IsOpen (from_normality hT (U, C)) := by

  intro hUC
  simp [from_normality, hUC]

  have h := Classical.choose_spec (hT U C hUC.left hUC.right.left hUC.right.right)
  exact h.left

lemma from_normality_prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)
    (U C : Set X)
    :
    normal_pair (U, C) → C ⊆ (from_normality hT (U, C)) ∧ closure (from_normality hT (U, C)) ⊆ U := by

  intro hUC
  simp [from_normality, hUC]

  have h := Classical.choose_spec (hT U C hUC.left hUC.right.left hUC.right.right)
  exact h.right


/-    DEFINICIÓN DE G

IDEA: primero definir G a partir de from_normality
sin necesidad de demostrar dentro de la definición
de G que los anteriores conjuntos definidos
cumplen las condiciones.

Después poder demostrar que se cumplen las condiciones.

Def: `G : ℕ → Set X`
  * `0 ↦ C2ᶜ`
  * `1 ↦ from_normality (C2ᶜ, C1)`
  * `n ↦ from_normality (G (s n), closure (G (r n)))`
-/


def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)

    : ℕ → Set X

    := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then from_normality hT (C2ᶜ, C1)
      else if n > 1 then
        let U := G hT C1 C2 (s n)
        let C := closure (G hT C1 C2 (r n))
        from_normality hT (U, C)
      else ∅

    decreasing_by
    · let s_prop := s_prop
      have aux : ∀ n > 1, s n < n
      · intro n hn
        specialize s_prop n hn
        simp at s_prop
        exact s_prop.left
      apply aux
      linarith

    · let r_prop := r_prop
      have aux : ∀ n > 1, r n < n
      · intro n hn
        specialize r_prop n hn
        simp at r_prop
        exact r_prop.left
      apply aux
      linarith

/-
`G_prop1`
Para cada n ∈ ℕ, G n es Abierto.
-/

lemma G_Prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, IsOpen (G hT C1 C2 n) := by

  intro n

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn hn

  · -- n = 0
    simp [hn, G]
    exact { isOpen_compl := hC2 }

  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn
  cases' cases with hn hn

  · -- n = 1
    simp [hn, G]
    apply from_normality_prop1
    constructor
    exact hC2
    constructor
    exact hC1
    exact hC1C2

  · -- n > 1
    have aux : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn
    have aux' : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn)

    rw [G]
    simp [hn, aux, aux']

    have cases :
      normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n))) ∨
      ¬ normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
      := by exact Classical.em (normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n))))

    cases' cases with op1 op2

    · apply from_normality_prop1
      exact op1

    · simp [from_normality, op2]


/-
`G_Prop2`
Para cada n > 1, se tiene:
  1. `closure (G (r n)) ⊆ G n`
  2. `closure (G n) ⊆ G (s n)`
-/

lemma G_Prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n > 1, closure (G hT C1 C2 (r n)) ⊆ (G hT C1 C2 n)
      ∧ closure (G hT C1 C2 n) ⊆ (G hT C1 C2 (s n)) := by

  intro n hn

  let P : ℕ → Prop := fun m ↦ m > 1
  apply my_stronger_induction n P
  exact hn
  simp [P]
  intro n hn hi

  have p := from_normality_prop2 hT

  have aux : n ≠ 0 := by exact Nat.not_eq_zero_of_lt hn
  have aux' : n ≠ 1 := by exact Ne.symm (Nat.ne_of_lt hn)

  have r_cases := r_options n hn
  cases' r_cases with hr hr

  · -- caso r n = 1

    have s_cases := s_options n hn
    cases' s_cases with hs hs

    · -- caso r n = 1, s n = 0

      let U := G hT C1 C2 n
      have U_def : U = G hT C1 C2 n := by rfl
      rw [← U_def]
      rw [G] at U_def
      simp [hn, aux, aux'] at U_def

      have some : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact isClosed_closure

        · have h : normal_pair (C2ᶜ, C1)
          · constructor
            exact hC2
            constructor
            exact hC1
            exact hC1C2

          simp [hr, hs, G, h, from_normality]

          have h' := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
          exact h'.right.right


      simp [from_normality, some] at U_def
      have some' := some
      apply p at some
      simp [from_normality, some'] at some
      rw [← U_def] at some
      exact some

    · -- caso r n = 1, s n > 1

      let U := G hT C1 C2 n
      have U_def : U = G hT C1 C2 n := by rfl
      rw [← U_def]
      rw [G] at U_def
      simp [hn, aux, aux'] at U_def

      have some : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact isClosed_closure

        · have hsn := (s_prop n hn).left
          simp at hsn
          have hrs : r n < s n := by linarith
          specialize hi (s n) hsn hs
          have aux := rn_eq_rsn n hn hs hrs
          rw [aux]
          exact hi.left

      simp [from_normality, some] at U_def
      have some' := some
      apply p at some
      simp [from_normality, some'] at some
      rw [← U_def] at some
      exact some


  · -- caso r n > 1
    have s_cases := s_options n hn
    cases' s_cases with hs hs

    · -- caso s n = 0, r n > 1

      let U := G hT C1 C2 n
      have U_def : U = G hT C1 C2 n := by rfl
      rw [← U_def]
      rw [G] at U_def
      simp [hn, aux, aux'] at U_def

      have some : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact isClosed_closure

        · have hrn := (r_prop n hn).left
          simp at hrn
          have hrs : s n < r n := by linarith
          specialize hi (r n) hrn hr
          have aux := sn_eq_srn n hn hr hrs
          rw [aux]
          exact hi.right

      simp [from_normality, some] at U_def
      have some' := some
      apply p at some
      simp [from_normality, some'] at some
      rw [← U_def] at some
      exact some

    · -- caso s n > 1, r n > 1

      let U := G hT C1 C2 n
      have U_def : U = G hT C1 C2 n := by rfl
      rw [← U_def]
      rw [G] at U_def
      simp [hn, aux, aux'] at U_def

      have some : normal_pair (G hT C1 C2 (s n), closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact isClosed_closure

        · have hrn := (r_prop n hn).left
          have hsn := (s_prop n hn).left
          simp at hrn hsn

          have cases := rs_options n hn
          cases' cases with hrs hrs

          · specialize hi (s n) hsn hs
            have aux := rn_eq_rsn n hn hs hrs
            rw [aux]
            exact hi.left

          · specialize hi (r n) hrn hr
            have aux := sn_eq_srn n hn hr hrs
            rw [aux]
            exact hi.right


      simp [from_normality, some] at U_def
      have some' := some
      apply p at some
      simp [from_normality, some'] at some
      rw [← U_def] at some
      exact some


/-
resumen
-/

example {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∃ G : ℕ → Set X,
      (
        (G 0 = C2ᶜ) ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)) ∧
        (∀ n, IsOpen (G n)) ∧
        (∀ n > 1, closure (G (r n)) ⊆ G n
          ∧ closure (G n) ⊆ G (s n))
      )

    := by

  use (G hT C1 C2)
  constructor
  · simp [G]

  constructor
  · have h : normal_pair (C2ᶜ, C1)
    · constructor; exact hC2
      constructor; exact hC1
      exact hC1C2
    simp [G, from_normality, h]

  constructor
  · exact fun n ↦ G_Prop1 hT C1 C2 hC1 hC2 hC1C2 n
  · exact fun n a ↦ G_Prop2 hT C1 C2 hC1 hC2 hC1C2 n a






/-
Ahora quiero ver que la propiedad se extiende, es decir:
`G_Prop2_ext`
Para cada n, m ∈ ℕ con `f n < f m`
se tiene `closure (G n) ⊆ G m`
-/

lemma G_Prop2_ext {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n m, f n < f m → closure (G hT C1 C2 n) ⊆ G hT C1 C2 m := by

  intro n m
  let P : ℕ × ℕ → Prop := fun (n, m) ↦ (f n < f m → closure (G hT C1 C2 n) ⊆ G hT C1 C2 m)
  have P_def : P (n, m) = (f n < f m → closure (G hT C1 C2 n) ⊆ G hT C1 C2 m) := by rfl
  rw [← P_def]
  apply WellFounded.induction lt_pair_wf
  simp [P]

  intro n m
  intro hi hnm
  simp [lt_pair] at hi

  have n_neq_m : n ≠ m
  · by_contra c
    simp [c] at hnm

  have lema1 : n ≠ 0
  · by_contra c
    apply congrArg f at c
    rw [f_prop.right.left] at c
    rw [c] at hnm
    have f_prop := (f_in_icc01 m).right
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hnm f_prop

  have lema2 : m ≠ 1
  · by_contra c
    apply congrArg f at c
    rw [f_prop.right.right] at c
    rw [c] at hnm
    have f_prop := (f_in_icc01 n).left
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false hnm f_prop

  have C_normal_pair : normal_pair (C2ᶜ, C1)
  · exact ⟨hC2, hC1, hC1C2⟩

  have G_Prop2 := G_Prop2 hT C1 C2 hC1 hC2 hC1C2

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn0 hn0

  · -- caso n = 0 (imposible)
    simp [hn0] at lema1

  · -- caso n > 0
    have cases : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
    cases' cases with hm0 hm0

    · -- caso n > 0, m = 0
      have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
      cases' cases with hn1 hn1

      · -- caso n = 1, m = 0
        simp [hn1, hm0, G, from_normality, C_normal_pair]
        exact (Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)).right.right

      · -- caso n > 1, m = 0
        -- inducción completa sobre n

        revert hnm hn1
        rw [hm0]

        apply my_strong_induction n

        intro n hi _ hn1

        have s_options := s_options n hn1
        cases' s_options with hs0 hs1

        · -- caso s(n) = 0
          rw [← hs0]
          exact (G_Prop2 n hn1).right

        · -- caso s(n) > 1
          trans closure (G hT C1 C2 (s n))
          · trans G hT C1 C2 (s n)
            · exact (G_Prop2 n hn1).right
            · exact subset_closure

          · have s_prop := (s_prop n hn1).left
            simp at s_prop
            have aux : f (s n) < f 0
            · simp [f_prop]
              apply lt_of_le_of_ne (f_in_icc01 (s n)).right
              rw [← f_prop.right.left]
              by_contra c
              apply f_prop.left.left at c
              simp [c] at hs1
            exact hi (s n) s_prop aux hs1


    · -- caso n > 0, m > 0
      have cases : m = 1 ∨ m > 1 := by exact LE.le.eq_or_gt hm0
      cases' cases with hm1 hm1

      · -- caso n > 0, m = 1 (imposible)
        simp [hm1] at lema2

      · -- caso n > 0, m > 1
        have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
        cases' cases with hn1 hn1

        · -- caso n = 1, m > 1
          -- inducción sobre m

          revert hnm hm1
          rw [hn1]

          apply my_strong_induction m

          intro m hi _ hm1

          have r_options := r_options m hm1
          cases' r_options with hr1 hr1

          · -- caso r(m) = 1
            rw [← hr1]
            exact (G_Prop2 m hm1).left

          · -- caso r(m) > 1
            trans G hT C1 C2 (r m)
            · have r_prop := (r_prop m hm1).left
              simp at r_prop
              have aux : f 1 < f (r m)
              · simp [f_prop]
                apply lt_of_le_of_ne (f_in_icc01 (r m)).left
                rw [← f_prop.right.right]
                by_contra c
                apply f_prop.left.left at c
                simp [c] at hr1
              exact hi (r m) r_prop aux hr1

            · trans closure (G hT C1 C2 (r m))
              · exact subset_closure
              · exact (G_Prop2 m hm1).left


        · -- caso n > 1, m > 1

          have s_prop := s_prop n hn1
          have r_prop := r_prop m hm1
          simp at s_prop r_prop

          have cases : f (s n) < f m ∨ f m ≤ f (s n) := by exact lt_or_le (f (s n)) (f m)
          cases' cases with h h

          · -- si f (s n) < f m
            trans closure (G hT C1 C2 (s n))
            · trans G hT C1 C2 (s n)
              · exact (G_Prop2 n hn1).right
              · exact subset_closure
            · exact hi (s n) m (by left; exact s_prop.left) h

          have cases : f m = f (s n) ∨ f m < f (s n)  := by exact (lt_or_eq_of_le h).symm
          cases' cases with h h

          · -- si f (s n) = f m
            apply f_prop.left.left at h
            rw [h]
            exact (G_Prop2 n hn1).right

          · -- si f m < f (s n)

            have cases : f n < f (r m) ∨ f (r m) ≤ f n := by exact lt_or_le (f n) (f (r m))
            cases' cases with h' h'

            · -- si f n < f (r m)
              trans G hT C1 C2 (r m)
              · exact hi n (r m) (by right; simp; exact r_prop.left) h'
              · trans closure (G hT C1 C2 (r m))
                · exact subset_closure
                · exact (G_Prop2 m hm1).left


            have cases : f (r m) = f n ∨ f (r m) < f n := by exact (lt_or_eq_of_le h').symm
            cases' cases with h' h'

            · -- si f n = f (r m)
              apply f_prop.left.left at h'
              rw [← h']
              exact (G_Prop2 m hm1).left

            · -- si f (r m) < f n (imposible!)
              have aux : n < m
              · by_contra c
                simp at c
                apply lt_of_le_of_ne at c
                specialize c n_neq_m.symm
                have aux := s_prop.right.right
                specialize aux m c hnm
                apply not_lt.mpr at aux
                exact aux h

              by_contra
              have aux' := r_prop.right.right
              specialize aux' n aux hnm
              apply not_lt.mpr at aux'
              exact aux' h'
