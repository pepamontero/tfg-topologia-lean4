
import Leantest.MyDefs.my_induction
import Leantest.MyDefs.my_rs_functions

lemma aux (R : ℕ) (n : ℕ) : n ∈ Finset.range R → n ∈ Finset.range (R+1) := by
  intro h
  simp at *
  linarith


lemma aux' (R : ℕ) (n : ℕ) : n ∈ Finset.range R → (n+1) ∈ Finset.range (R+1) := by
  intro h
  simp at *
  linarith

/-
given F : ℕ → ℕ a function
and k a natural number,
return the function F^k
-/

def apply_k_times (F : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  match k with
  | 0 => fun n ↦ 1
  | 1 => fun n ↦ F n
  | k + 2 => fun n ↦ F ((apply_k_times F (k+1)) n)

def g : ℕ → ℕ := fun n ↦ n^2

#eval g 3

#eval (apply_k_times g 3) 3

lemma apply_k_times_prop (F : ℕ → ℕ) (k : ℕ) (n : ℕ) :
    (apply_k_times F (k+2)) n = F ((apply_k_times F (k+1)) n) := by
  rfl

lemma apply_k_times_prop' (F : ℕ → ℕ) (k : ℕ) (hk : k > 1) (n : ℕ) :
    F ((apply_k_times F (k)) n) = (apply_k_times F (k+1)) n := by
  cases' k with k
  · simp at hk

  cases' k with k
  · simp [apply_k_times]
  · simp [apply_k_times]

lemma apply_k_times_prop'' (F : ℕ → ℕ) (k : ℕ) (hk : k > 1) (n : ℕ) :
    (apply_k_times F (k)) (F n) = (apply_k_times F (k+1)) n := by

  induction' hk with w hw hi
  · simp [apply_k_times]
  · simp at *
    simp [apply_k_times]
    rw [← hi]
    have aux := apply_k_times_prop' F w (by linarith) (F n)
    rw [← aux]







noncomputable def rk (k : ℕ) : ℕ → ℕ := apply_k_times r k

lemma lesser_r_finite_steps (n m : ℕ) (hn : n > 1) (hm : m > 1) :
    ∃ k > 0, (rk k) m < n := by

  let P : ℕ → Prop := fun l ↦ l > 1
  have hP : P m := by exact hm

  let Q : ℕ → Prop := fun l ↦ ∃ k > 0, rk k l < n
  have hQ : Q m = (∃ k >0, rk k m < n) := by rfl

  apply my_stronger_induction m P Q hP

  simp [P, Q]
  intro m hm hi

  have hrm := (r_prop m hm).left
  simp at hrm

  have cases : m ≤ n ∨ n < m := by exact le_or_lt m n
  cases' cases with hnm hnm

  · use 1
    simp [rk, apply_k_times]
    linarith

  · have cases := r_options m hm
    cases' cases with hrm1 hrm1

    · use 1
      simp [rk, apply_k_times]
      simp [hrm1]
      exact hn

    · specialize hi (r m) hrm hrm1
      cases' hi with k hk

      have cases : k = 1 ∨ k > 1 := by exact LE.le.eq_or_gt hk.left
      cases' cases with hk1 hk1

      · simp [hk1, rk, apply_k_times] at hk
        use 2
        simp [rk, apply_k_times]
        exact hk

      · have aux := apply_k_times_prop'' r k hk1 m
        simp [rk] at hk
        rw [aux] at hk
        use k+1
        simp [rk]
        exact hk.right



#check Finset.inf

lemma finite_r_jumps : ∀ n > 1, ∀ m > 1,n < m →
    ∃ R : ℕ, ∃ F : ℕ → ℕ,
      F 0 = n ∧
      F R = m ∧
      (∀ k < R, F k < F (k+1)) ∧
      ∀ k < R, F k = r (F (k+1))
    := by

  intro n hn m hm hnm

  let P : ℕ → ℕ → Prop := fun i ↦ fun j ↦ i > 1 ∧ j > 1 ∧ i < j
  have hP : P n m := by constructor; exact hn; constructor; exact hm; exact hnm

  let Q : ℕ → ℕ → Prop := fun i ↦ fun j ↦ ∃ R : ℕ, ∃ F : ℕ → ℕ,
      F 0 = i ∧
      F R = j ∧
      (∀ k < R, F k < F (k+1)) ∧
      ∀ k < R, F k = r (F (k+1))
  have hQ : Q n m = (∃ R : ℕ, ∃ F : ℕ → ℕ,
      F 0 = n ∧
      F R = m ∧
      (∀ k < R, F k < F (k+1)) ∧
      (∀ k < R, F k = r (F (k+1)))) := by rfl

  apply my_stronger_double_induction n m P Q hP



  let P : ℕ → Prop := fun k ↦ k > 1 ∧ n < k
  have hP : P m := by constructor; exact hm; exact hnm

  let Q : ℕ → Prop := fun l ↦ ∃ R : ℕ, ∃ F : ℕ → ℕ,
      F 0 = n ∧
      F R = l ∧
      (∀ k < R, F k < F (k+1)) ∧
      ∀ k < R, F k = r (F (k+1))
  have hQ : Q m = (∃ R : ℕ, ∃ F : ℕ → ℕ,
      F 0 = n ∧
      F R = m ∧
      (∀ k < R, F k < F (k+1)) ∧
      (∀ k < R, F k = r (F (k+1)))) := by rfl

  apply my_stronger_induction m P Q hP

  simp [P, Q]
  intro m hm hnm hi

  have cases : r m = n ∨ r m ≠ n := by exact eq_or_ne (r m) n
  cases' cases with h1 h2

  · use 1

    let F : ℕ → ℕ := fun k ↦
      if k = 0 then n
      else if k = 1 then m
      else 0

    use F
    constructor

    · simp [F]
    constructor
    · simp [F]
    constructor
    · intro k hk
      simp at hk
      simp [hk, F]
      exact hnm
    · intro k hk
      simp at hk
      simp [hk, F]
      simp [h1]

  · have hR := lesser_r_finite_steps n m hn hm
    cases' hR with R hR

    let F : ℕ → ℕ := fun k ↦
      if k = 0


    sorry

  have cases : r m < n ∨ n < r m := by exact Nat.lt_or_gt_of_ne h2
  cases' cases with h1 h2

  · -- aquí está el caso más difícil?

    sorry

  · -- este es el caso fácil
    -- usamos la inducción

    have hrm := (r_prop m hm).left
    simp at hrm
    have hrm1 : r m > 1
    · have r_options := r_options m hm
      have aux : r m ≠ 1
      by_contra c
      simp [c] at h2
      simp [h2] at hn
      linarith

    specialize hi (r m) hrm hrm1 h2
    cases' hi with R hR
    cases' hR with F hF
    use R+1

    let F' : ℕ → ℕ := fun k ↦
      if k < R+1 then F k
      else m
    use F'

    constructor
    · simp [F']
      exact hF.left
    constructor
    · simp [F']
    constructor
    · intro k hk
      simp [F', hk]
      have cases : k < R ∨ k = R := by exact Nat.lt_succ_iff_lt_or_eq.mp hk
      cases' cases with hkR hkR
      · simp [hkR]
        exact hF.right.right.left k hkR
      · simp [hkR]
        rw [hF.right.left]
        exact hrm
    · intro k hk
      simp [F', hk]
      have cases : k < R ∨ k = R := by exact Nat.lt_succ_iff_lt_or_eq.mp hk
      cases' cases with hkR hkR
      · simp [hkR]
        exact hF.right.right.right k hkR
      · simp [hkR]
        rw [hF.right.left]
