import Leantest.Separation.normal
import Leantest.MyDefs.my_rs_functions
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
  C ⊆ V ⊆ Closure V ⊆ U
-/

def normal_pair {X : Type} [T : TopologicalSpace X]
    : (Set X × Set X) → Prop := fun (U, C) ↦ (IsOpen U ∧ IsClosed C ∧ C ⊆ U)

noncomputable def from_normality {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
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
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (U C : Set X)
    :
    normal_pair (U, C) → IsOpen (from_normality hT (U, C)) := by

  intro hUC
  simp [from_normality, hUC]

  have h := Classical.choose_spec (hT U C hUC.left hUC.right.left hUC.right.right)
  exact h.left

lemma from_normality_prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (U C : Set X)
    :
    normal_pair (U, C) → C ⊆ (from_normality hT (U, C)) ∧ Closure (from_normality hT (U, C)) ⊆ U := by

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
  * `n ↦ from_normality (G (s n), Closure (G (r n)))`
-/


def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)

    : ℕ → Set X

    := fun n ↦
      if n = 0 then C2ᶜ
      else if n = 1 then from_normality hT (C2ᶜ, C1)
      else if n > 1 then
        let U := G hT C1 C2 (s n)
        let C := Closure (G hT C1 C2 (r n))
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
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

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
      normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n))) ∨
      ¬ normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n)))
      := by exact Classical.em (normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n))))

    cases' cases with op1 op2

    · apply from_normality_prop1
      exact op1

    · simp [from_normality, op2]


/-
`G_Prop2`
Para cada n > 1, se tiene:
  1. `Closure (G (r n)) ⊆ G n`
  2. `Closure (G n) ⊆ G (s n)`
-/

lemma G_Prop2 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n > 1, Closure (G hT C1 C2 (r n)) ⊆ (G hT C1 C2 n)
      ∧ Closure (G hT C1 C2 n) ⊆ (G hT C1 C2 (s n)) := by

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

      have some : normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact closure_is_closed (G hT C1 C2 (r n))

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

      have some : normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact closure_is_closed (G hT C1 C2 (r n))

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

      have some : normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact closure_is_closed (G hT C1 C2 (r n))

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

      have some : normal_pair (G hT C1 C2 (s n), Closure (G hT C1 C2 (r n)))
      · constructor
        · apply G_Prop1
          exact hC1; exact hC2; exact hC1C2
        constructor

        · exact closure_is_closed (G hT C1 C2 (r n))

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
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

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
        (∀ n > 1, Closure (G (r n)) ⊆ G n
          ∧ Closure (G n) ⊆ G (s n))
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
ahora quiero ver que la propiedad se extiende...
-/

lemma G_Prop2' {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n m, f n < f m → Closure (G hT C1 C2 n) ⊆ G hT C1 C2 m := by

  sorry

/-
Después podría definir F : ℚ → Set X
-/

def H {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)

    : ℚ → Set X := fun q ↦

  if q < 0 then ∅
  else if h : 0 ≤ q ∧ q ≤ 1 then G hT C1 C2 (f_inv ⟨q, h⟩)
  else Set.univ


lemma H_Prop {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    H hT C1 C2 1 = C2ᶜ ∧
    H hT C1 C2 0 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2) ∧
    (∀ q, IsOpen (H hT C1 C2 q)) ∧
    (∀ p q : ℚ, p < q → Closure (H hT C1 C2 p) ⊆ H hT C1 C2 q)
    := by

  constructor

  · have c : ¬ (1 : ℚ) < (0 : ℚ) := by linarith
    simp [H, c]
    have aux := f_inv_1
    simp at aux
    rw [aux]
    simp [G]

  constructor

  · simp [H]
    have aux := f_inv_0
    simp at aux
    rw [aux]
    have aux : normal_pair (C2ᶜ, C1)
    · constructor; exact hC2
      constructor; exact hC1
      exact hC1C2
    simp [G, from_normality, aux]

  constructor

  · intro q
    have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_le q 0
    cases' cases with hq hq

    · -- q < 0 -> H q = ∅ (trivial)
      simp [H, hq]

    have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
    have aux : ¬ q < 0 := by linarith
    cases' cases with hq' hq'

    · -- 0 ≤ q ≤ 1 -> usando la prop. de G
      simp [H, aux, hq, hq']
      apply G_Prop1 hT C1 C2 hC1 hC2 hC1C2

    · -- q > 1 -> H q = X (trivial)
      simp [H]
      have aux' : ¬ (0 ≤ q ∧ q ≤ 1)
      · simp at aux
        simp [aux]
        exact hq'
      simp [H, aux, aux']

  · intro p q hpq

    have cases : q < 0 ∨ q ≥ 0 := by exact lt_or_le q 0
    cases' cases with hq hq

    · -- q < 0 -> p < q < 0 -> H p = H q = ∅
      have aux : p < 0 := by linarith
      simp [H, aux, hq]
      exact closure_of_empty

    have cases : q ≤ 1 ∨ q > 1 := by exact le_or_lt q 1
    have aux : ¬ q < 0 := by linarith
    cases' cases with hq' hq'

    · -- 0 ≤ q ≤ 1

      have cases : p < 0 ∨ p ≥ 0 := by exact lt_or_le p 0
      cases' cases with hp hp

      · -- p < 0 -> H p = ∅ (trivial)
        simp [H, hp, closure_of_empty]

      have cases : p ≤ 1 ∨ p > 1 := by exact le_or_lt p 1
      have aux' : ¬ p < 0 := by linarith
      cases' cases with hp' hp'

      · -- 0 ≤ p < q ≤ 1
        simp [H, aux, aux', hp, hp', hq, hq']
        apply G_Prop2' hT C1 C2 hC1 hC2 hC1C2
        have hfp := f_inv_prop.right ⟨p, by
          constructor
          exact hp
          exact hp'⟩
        have hfq := f_inv_prop.right ⟨q, by
          constructor
          exact hq
          exact hq'⟩
        rw [hfp, hfq]
        simp
        exact hpq

      · -- p > 1 (imposible)
        linarith

    · -- q > 1 -> H q = X (trivial)
      have aux' : ¬ q ≤ 1 := by linarith
      simp [H, aux, aux', hq, hq']
