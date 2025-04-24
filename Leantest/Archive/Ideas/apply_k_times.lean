import Leantest.MyDefs.my_rs_functions


-- DEFINICIONES

def apply_k_times (F : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  match k with
  | 0 => fun n ↦ n
  | 1 => fun n ↦ F n
  | k + 2 => fun n ↦ F ((apply_k_times F (k+1)) n)

noncomputable def rPow (k : ℕ) : ℕ → ℕ := apply_k_times r k

noncomputable def sPow (k : ℕ) : ℕ → ℕ := apply_k_times s k

-- PROPIEDADES GENERALES

lemma apply_k_times_prop (F : ℕ → ℕ) (k : ℕ) (n : ℕ) :
    (apply_k_times F (k+2)) n =
      F ((apply_k_times F (k+1)) n) := by
  rfl


lemma apply_k_times_prop' (F : ℕ → ℕ) (k : ℕ) (n : ℕ) :
    F ((apply_k_times F (k)) n) =
      (apply_k_times F (k+1)) n := by
  cases' k with k
  · simp [apply_k_times]
  · simp [apply_k_times]


lemma apply_k_times_prop'' (F : ℕ → ℕ) (k : ℕ) (n : ℕ) :
    (apply_k_times F (k)) (F n) =
      (apply_k_times F (k+1)) n := by

  induction' k with k hi
  · simp [apply_k_times]
  · simp [apply_k_times]
    rw [← hi]
    exact (apply_k_times_prop' F k (F n)).symm


-- PROPIEDADES DE R POW Y S POW

lemma rk_beq_1 (n k : ℕ) (hn : n > 1)
    : rPow k n ≥ 1 := by

  induction' k with k hi

  · simp [rPow, apply_k_times]
    exact Nat.one_le_of_lt hn

  · by_contra c
    simp at c

    have aux := apply_k_times_prop' r k n
    rw [← rPow, ← rPow] at aux
    rw [← aux] at c

    have cases : rPow k n = 1 ∨ rPow k n > 1 := by exact LE.le.eq_or_gt hi
    cases' cases with h h
    · rw [h] at c
      have h' : r 1 = 1
      simp [r]
      simp [h'] at c

    · have aux := r_options (rPow k n) h
      simp [c] at aux


lemma rk_leq_n (n k : ℕ) (hn : n > 1)
    : rPow k n ≤ n := by

  induction' k with k hi

  · simp [rPow, apply_k_times]

  · have aux' := rk_beq_1 n k hn
    have aux := apply_k_times_prop' r k n
    rw [← rPow, ← rPow] at aux
    rw [← aux]
    have cases : rPow k n = 1 ∨ rPow k n > 1 := by exact LE.le.eq_or_gt aux'
    cases' cases with h h
    · rw [h]
      simp [r]
      exact Nat.one_le_of_lt hn
    · trans rPow k n
      · have aux := (r_prop (rPow k n) h).left
        simp at aux
        exact Nat.le_of_succ_le aux
      · exact hi


lemma frk_leq (n k : ℕ)
    : f (rPow k n) ≤ f n := by

  induction' k with k hi

  · simp [rPow, apply_k_times]

  · trans f (rPow k n)
    · have aux := apply_k_times_prop' r k n
      rw [← rPow, ← rPow] at aux
      rw [← aux]
      exact fr_leq (rPow k n)

    · exact hi



lemma frk_lt_fn (n k : ℕ) (hk : k > 0) (hn : n > 1)
    : f (rPow k n) < f n := by

  apply lt_of_le_of_ne
  · exact frk_leq n k
  · by_contra c

    apply f_prop.left.left at c

    induction' hk with k hk hi

    · simp [rPow, apply_k_times] at c
      have aux := (r_prop n hn).right.left
      simp [c] at aux

    · simp at *
      have aux := apply_k_times_prop' r k n
      rw [← rPow, ← rPow] at aux
      rw [← aux] at c

      have aux : 1 < rPow k n
      · apply lt_of_le_of_ne
        · exact rk_beq_1 n k hn
        · by_contra c'
          rw [← c'] at c
          simp [r] at c
          simp [c] at hn

      have sos := (r_prop (rPow k n) aux).left
      simp at sos
      rw [c] at sos
      have aux := rk_leq_n n k hn
      apply not_le_of_lt at sos
      exact sos aux



/-
 Resultado: get to n in k steps
-/

lemma lesser_r_finite_steps (n m : ℕ) (hn : n > 1) (hm : m > 1) :
    ∃ k > 0, (rPow k) m < n := by

  let P : ℕ → Prop := fun l ↦ l > 1
  have hP : P m := by exact hm

  let Q : ℕ → Prop := fun l ↦ ∃ k > 0, rPow k l < n

  apply my_stronger_induction m P Q hP

  simp [P, Q]
  intro m hm hi

  have hrm := (r_prop m hm).left
  simp at hrm

  have cases : m ≤ n ∨ n < m := by exact le_or_lt m n
  cases' cases with hnm hnm

  · use 1
    simp [rPow, apply_k_times]
    linarith

  · have cases := r_options m hm
    cases' cases with hrm1 hrm1

    · use 1
      simp [rPow, apply_k_times]
      simp [hrm1]
      exact hn

    · specialize hi (r m) hrm hrm1
      cases' hi with k hk

      have cases : k = 1 ∨ k > 1 := by exact LE.le.eq_or_gt hk.left
      cases' cases with hk1 hk1

      · simp [hk1, rPow, apply_k_times] at hk
        use 2
        simp [rPow, apply_k_times]
        exact hk

      · have aux := apply_k_times_prop'' r k m
        simp [rPow] at hk
        rw [aux] at hk
        use k+1
        simp [rPow]
        exact hk.right


/-
lemas auxiliares
-/

lemma aux1 (n m : ℕ) (hm : m > 1)
    (h : n < m)
    (h' : f n < f m)
    : f n ≤ f (r m) := by
  have r_prop := (r_prop m hm).right.right
  simp at r_prop
  exact r_prop n h h'

lemma aux1' (n m : ℕ) (hn : n > 1)
    (h : m < n)
    (h' : f n < f m)
    : f (s n) ≤ f m := by
  have s_prop := (s_prop n hn).right.right
  simp at s_prop
  exact s_prop m h h'



lemma aux2 (m : ℕ) (hm : m > 1) :
    ∃ k, rPow k m = 1 := by

  let P : ℕ → Prop := fun n ↦ n > 1
  apply my_stronger_induction m P
  exact hm
  simp [P]
  intro m hm hi

  have cases := r_options m hm
  cases' cases with hr hr

  · use 1
    simp [rPow, apply_k_times]
    exact hr

  · have hr' := (r_prop m hm).left
    simp at hr'
    specialize hi (r m) hr' hr
    cases' hi with k hk
    use k+1
    simp [rPow] at *
    have aux := apply_k_times_prop'' r k m
    rw [← aux]
    exact hk

lemma aux2' (m : ℕ) (hm : m > 1) :
    ∃ k, sPow k m = 0 := by

  let P : ℕ → Prop := fun n ↦ n > 1
  apply my_stronger_induction m P
  exact hm
  simp [P]
  intro m hm hi

  have cases := s_options m hm
  cases' cases with hr hr

  · use 1
    simp [sPow, apply_k_times]
    exact hr

  · have hr' := (s_prop m hm).left
    simp at hr'
    specialize hi (s m) hr' hr
    cases' hi with k hk
    use k+1
    simp [sPow] at *
    have aux := apply_k_times_prop'' s k m
    rw [← aux]
    exact hk


/-
  Decimos que vamos de n a m en un paso
  si m = r(n) o m = s(n)
-/
def step (n m : ℕ) : Prop :=
  m = r n ∨ m = s n




example (n m : ℕ) (hn : n > 1) (hm : m > 1)
    (h : n < m)
    (h' : f n < f m)
    :
    ∃ k > 0, f (s n) ≤ f (rPow k m) := by

  let P : ℕ → Prop := fun l ↦ l > 1
  have hP : P m := by exact hm

  apply my_stronger_induction m P
  exact hP
  simp [P]

  intro m hm hi

  let k := Classical.choose (lesser_r_finite_steps n m hn hm)
  have k_def : k = Classical.choose (lesser_r_finite_steps n m hn hm) := by rfl
  let k_prop := Classical.choose_spec (lesser_r_finite_steps n m hn hm)
  rw [← k_def] at k_prop

  use k
  constructor

  · exact k_prop.left

  · have r_prop := r_prop

    sorry



-- RESULTADO PRINCIPAL

example (a b : ℝ) : a ≤ b → a ≠ b → a < b := by exact fun a_1 a_2 ↦ lt_of_le_of_ne a_1 a_2

example (n m : ℕ)
    (hn : n > 1) (hm : m > 1)
    (h : f n < f m)

    :

    ∃ k l : ℕ, sPow k n = rPow l m

    := by

  let P : ℕ → ℕ → Prop := fun k ↦ fun l ↦
    (k > 1) ∧ (l > 1) ∧ (f k < f l)

  have hP : P n m
  · constructor; exact hn
    constructor; exact hm; exact h

  apply my_stronger_double_induction' n m P
  exact hP

  simp [P]
  intro n m hn hm h hi

  have r_prop := r_prop m hm
  have s_prop := s_prop n hn
  simp at r_prop s_prop

  have cases := s_options n hn
  cases' cases with hsn hsn

  · -- caso s n = 0

    sorry



  have perfect_case : (s n > 1) ∧ (r m > 1) ∧
    f (s n) < f (r m)
  sorry

  specialize hi
    (s n) s_prop.left
    (r m) r_prop.left
    perfect_case.left
    perfect_case.right.left
    perfect_case.right.right

  cases' hi with k hi
  cases' hi with l hi
  use k+1
  use l+1

  simp [sPow, rPow] at *
  have p1 := apply_k_times_prop'' s k n
  have p2 := apply_k_times_prop'' r l m
  rw [← p1, ← p2]
  exact hi
