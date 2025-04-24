import Leantest.MyDefs.my_rs_functions
import Leantest.MyDefs.my_induction

/-
the objetive of this file is to prove:
r' : ℕ → ℕ → Prop := r' n m = r n = m
is a well founded property -/


def lt : ℕ → ℕ → Prop := fun n ↦ fun m ↦ n < m

def lt_wf : WellFoundedRelation ℕ where
  rel := lt
  wf := by
    apply WellFounded.intro
    intro n
    induction n with
    | zero      =>
      apply Acc.intro 0
      intro _ h
      apply absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      apply Acc.intro (Nat.succ n)
      intro m h
      have : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)
      match this with
      | Or.inl e => subst e; assumption
      | Or.inr e => exact Acc.inv ih e

def my_lt_wf : WellFoundedRelation ℕ where
  rel := lt
  wf := by
    apply WellFounded.intro
    intro n
    induction' n with n ih

    · apply Acc.intro 0
      intro y hy
      simp [lt] at hy

    · apply Acc.intro
      intro m h
      have this : m = n ∨ m < n := Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h)

      cases' this with h1 h2
      · -- si m = n
        rw [h1]
        exact ih

      · -- si m < n
        exact Acc.inv ih h2



def R : ℕ → ℕ → Prop :=
  fun n ↦ fun m ↦
    if m = 0 then False
    else n = r m


#check IsWellFounded
#check WellFounded

lemma R_is_wf : WellFounded R := by
  apply WellFounded.intro
  intro n
  apply my_strong_induction n
  intro n hi

  apply Acc.intro
  intro m hm
  simp [R] at hm
  cases' hm with hn hm

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn0 hn0

  · simp [hn0] at hn

  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
  cases' cases with hn1 hn1

  · rw [hn1, r] at hm
    specialize hi 0 (by linarith)
    rw [hm]
    exact hi

  · have r_prop := (r_prop n hn1).left
    simp at r_prop
    exact hi m (by linarith)

def Rwf : WellFoundedRelation ℕ where
  rel := R
  wf := R_is_wf

def S : ℕ → ℕ → Prop :=
  fun n ↦ fun m ↦
    if m = 0 then False
    else n = s m

lemma S_is_wf : WellFounded S := by
  apply WellFounded.intro
  intro n
  apply my_strong_induction n
  intro n hi

  apply Acc.intro
  intro m hm
  simp [S] at hm
  cases' hm with hn hm

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn0 hn0

  · simp [hn0] at hn

  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn0
  cases' cases with hn1 hn1

  · rw [hn1, s] at hm
    specialize hi 0 (by linarith)
    rw [hm]
    exact hi

  · have s_prop := (s_prop n hn1).left
    simp at s_prop
    exact hi m (by linarith)

def Swf : WellFoundedRelation ℕ where
  rel := S
  wf := S_is_wf


-- una idea un poco loca

def X : (ℕ × ℕ) → (ℕ × ℕ) → Prop :=
  fun (k, l) ↦
    fun (n, m) ↦
      S k n ∧ R l m ∧ (f n ≤ f l ∨ f k ≤ f m)

lemma X_is_wf : WellFounded X := by
  -- es que realmente no es esta la movida jajaja
