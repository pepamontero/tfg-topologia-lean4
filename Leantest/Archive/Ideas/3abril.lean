import Leantest.Separation.def_G
import Leantest.Archive.Ideas.apply_k_times

example (n m : ℕ)
    (hn : n > 1)
    (hm : m > 1)
    (h : f n < f m)
    (h' : f (r m) < f (s n))
    :
    ¬ (f n < f (r m) ∧
      f (s n) < f m)
    := by

  by_contra c
  cases' c with h1 h2

  have r_prop := r_prop m hm
  have s_prop := s_prop n hn
  simp at r_prop s_prop

  have cases : n < m ∨ m ≤ n := by exact Nat.lt_or_ge n m
  cases' cases with hnm hnm

  · -- n < m
    have r_prop := r_prop.right.right
    specialize r_prop (s n) (by
      trans n
      exact s_prop.left
      exact hnm)
      h2
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h' r_prop

  have cases : m = n ∨ m < n := by exact Nat.eq_or_lt_of_le hnm
  cases' cases with hnm hnm

  · simp [hnm] at h

  · -- m < n
    have s_prop := s_prop.right.right
    specialize s_prop (r m) (by
      trans m
      exact r_prop.left
      exact hnm)
      h1
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h' s_prop

  
    
   

  sorry


example (a b : ℝ) : a < b → a ≤ b := by exact fun a_1 ↦ le_of_lt a_1

#check WellFounded.induction

example (n m : ℕ)
    :
    n > 1 → m > 1 → f n ≤ f m →
    ∃ k l : ℕ, rPow k m = sPow l n
    := by

  apply my_strong_double_induction n m

  intro n m
  constructor

  · intro hi hn hm h
    simp [hm] at hi

    have s_options := s_options n hn
    have r_options := r_options m hm
    have s_prop := s_prop n hn
    have r_prop := r_prop m hm
    simp at s_prop r_prop

    have cases : f n = f m ∨ f n < f m := by exact Or.symm (Decidable.lt_or_eq_of_le h)
    cases' cases with h h

    · 
      apply f_prop.left.left at h
      use 0
      use 0
      simp [rPow, sPow, apply_k_times]
      exact h.symm

    · 
      have perf_scenario : s n > 1 ∧ r m > 1 := by sorry

      have cases : f (s n) ≤ f m ∨ f m < f (s n) := by exact le_or_lt (f (s n)) (f m)
      cases' cases with h' h'

      have cases : f (s n) = f m ∨ f (s n) < f (m) := by exact Or.symm (Decidable.lt_or_eq_of_le h')
      cases' cases with h' h'

      · apply f_prop.left.left at h'
        use 0
        use 1
        simp [rPow, sPow, apply_k_times]
        exact h'.symm

      · specialize hi
          (s n) s_prop.left
          perf_scenario.left
          (by exact le_of_lt h')
        cases' hi with k hi
        cases' hi with l hi
        use k
        use l+1
        rw [hi]

        have aux := apply_k_times_prop''
        specialize aux s l n
        rw [← sPow, ← sPow] at aux
        rw [← aux]

      · have aux : m < n
        · by_contra c
          simp at c
          have cases : n = m ∨ n < m := by exact Nat.eq_or_lt_of_le c
          cases' cases with c c
          · simp [c] at h
          · 
        sorry
    sorry 

  sorry


example (n m : ℕ)
    :
    n > 1 → m > 1 → f n < f m →
    ∃ k l : ℕ, rPow k m = sPow l n
    := by

  apply my_strong_double_induction' n m

  intro n m hi hn hm h

  have s_options := s_options n hn
  have r_options := r_options m hm
  have s_prop := s_prop n hn
  have r_prop := r_prop m hm
  simp at s_prop r_prop

  cases' s_options with hsn hsn
  · -- caso s n = 0
    sorry


  · -- caso s n > 1
    cases' r_options with hrm hrm

    · -- caso r m = 1
      sorry

    · -- caso r m > 1

      have aux : f (s n) ≤ f (r m)
      ·

        sorry

      have cases : f (s n) = f (r m) ∨ f (s n) < f (r m) := by exact Or.symm (Decidable.lt_or_eq_of_le aux)
      cases' cases with h' h'

      · -- f (s n) = f (r m)
        apply f_prop.left.left at h'
        use 1
        use 1
        simp [rPow, sPow, apply_k_times]
        exact h'.symm

      · -- f (s n) < f (r m)
        specialize hi
          (s n) s_prop.left
          (r m) r_prop.left
          hsn hrm
          h'

        cases' hi with k hi
        cases' hi with l hi
        use k+1
        use l+1

        have aux := apply_k_times_prop''
        specialize aux r k m
        rw [← rPow, ← rPow] at aux
        rw [← aux]

        have aux := apply_k_times_prop''
        specialize aux s l n
        rw [← sPow, ← sPow] at aux
        rw [← aux]

        exact hi
