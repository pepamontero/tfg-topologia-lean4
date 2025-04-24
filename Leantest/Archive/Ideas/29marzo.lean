import Leantest.Archive.Ideas.apply_k_times

def rel : ℕ → ℕ → Prop :=
  fun n ↦ fun m ↦ n = r m ∨ m = s n

example (a b : ℝ) : a ≤ b → a ≠ b → a < b := by exact fun a_1 a_2 ↦ lt_of_le_of_ne a_1 a_2

lemma fnm_cases (n m : ℕ) (h : f n < f m) :
    (n = 1 ∧ m = 0) ∨
    (n = 1 ∧ m > 1) ∨
    (n > 1 ∧ m = 0) ∨
    (n > 1 ∧ m > 1) := by

  have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  cases' cases with hn hn

  · -- n = 0 (imposible)
    rw [hn, f_prop.right.left] at h
    have aux := (f_in_icc01 m).right
    by_contra
    exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h aux

  -- n > 0
  have cases : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt hn
  cases' cases with hn hn

  · -- n = 1

    have cases : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
    cases' cases with hm hm

    · -- m = 0
      simp [hn, hm]

    -- m > 0
    have cases : m = 1 ∨ m > 1 := by exact LE.le.eq_or_gt hm
    cases' cases with hm hm

    · -- m = 1 (imposible)
      rw [hm, f_prop.right.right] at h
      have aux := (f_in_icc01 n).left
      by_contra
      exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h aux

    · -- m > 1
      simp [hn, hm]

  · -- n > 1

    have cases : m = 0 ∨ m > 0 := by exact Nat.eq_zero_or_pos m
    cases' cases with hm hm

    · -- m = 0
      simp [hn, hm]

    -- m > 0
    have cases : m = 1 ∨ m > 1 := by exact LE.le.eq_or_gt hm
    cases' cases with hm hm

    · -- m = 1 (imposible)
      rw [hm, f_prop.right.right] at h
      have aux := (f_in_icc01 n).left
      by_contra
      exact Std.Tactic.BVDecide.Reflect.Bool.false_of_eq_true_of_eq_false h aux

    · -- m > 1
      simp [hn, hm]



lemma rel_prop (n m : ℕ) (h : f n < f m)
    :
    rel n m ∨
    ∃ k < max n m, (
      (rel n k ∧ f k < f m)
      ∨ (f n < f k ∧ rel k m)
    ) := by

  have cases := fnm_cases n m h
  cases' cases with hnm cases

  · -- n = 1, m = 0
    left
    simp [hnm, rel, r]

  cases' cases with hnm cases

  · -- n = 1, m > 1
    have cases : rel n m ∨ ¬ rel n m := by exact Classical.em (rel n m)
    cases' cases with h' h'
    all_goals simp [h']

    use r m
    constructor
    · right
      have aux := (r_prop m hnm.right).left
      simp at aux; exact aux

    · right
      constructor
      · simp [hnm]
        apply lt_of_le_of_ne
        · rw [f_prop.right.right]
          exact (f_in_icc01 (r m)).left
        · by_contra c
          apply f_prop.left.left at c
          simp [rel, hnm] at h'
          exact h'.left c
      · simp [rel]

  cases' cases with hnm hnm

  · -- n > 1, m = 0
    have cases : rel n m ∨ ¬ rel n m := by exact Classical.em (rel n m)
    cases' cases with h' h'
    all_goals simp [h']

    use s n
    constructor
    · left
      have aux := (s_prop n hnm.left).left
      simp at aux; exact aux

    · left
      constructor
      · simp [rel]
      · simp [hnm]
        apply lt_of_le_of_ne
        · rw [f_prop.right.left]
          exact (f_in_icc01 (s n)).right
        · by_contra c
          apply f_prop.left.left at c
          simp [rel, hnm] at h'
          exact h'.right c.symm

  · -- n > 1, m > 1
    cases' hnm with hn hm

    have cases : rel n m ∨ ¬ rel n m := by exact Classical.em (rel n m)
    cases' cases with h' h'

    · left; exact h'

    · right
      simp [rel] at h'

      have cases : n < m ∨ n ≥ m := by exact Nat.lt_or_ge n m
      cases' cases with hnm hnm

      · -- n < m

        use (r m)
        constructor
        · simp
          right
          have aux := (r_prop m hm).left
          simp at aux; exact aux

        · right
          constructor
          · apply lt_of_le_of_ne

            · apply (r_prop m hm).right.right
              · simp; exact hnm
              · exact h

            · by_contra c
              apply f_prop.left.left at c
              simp [c] at h'

          · simp [rel]

      have cases : n = m ∨ n > m := by exact LE.le.eq_or_gt hnm
      cases' cases with hnm hnm

      · -- n = m (imposible)
        simp [hnm] at h

      · -- m < n

        use (s n)
        constructor
        · simp
          left
          have aux := (s_prop n hn).left
          simp at aux; exact aux

        · left
          constructor
          · simp [rel]
          · apply lt_of_le_of_ne

            · apply (s_prop n hn).right.right
              · simp; exact hnm
              · exact h

            · by_contra c
              apply f_prop.left.left at c
              simp [c] at h'


lemma rel_big_prop (n m : ℕ) (h : f n < f m)
    :
    ∃ k : ℕ, ∃ K : ℕ → ℕ, (
      (K 0 = n) ∧
      (K k = m) ∧
      (∀ i < k, rel (K i) (K (i+1)))
    )
    := by

  let P : ℕ → ℕ → Prop := fun n ↦ fun m ↦
    (f n < f m)


  apply my_stronger_double_induction n m P

  · exact h

  simp [P]
  intro n m h

  have cases := fnm_cases n m h
  cases' cases with hnm cases

  · --
    sorry

  cases' cases with hnm cases

  · --
    sorry

  cases' cases with hnm hnm

  · --
    sorry


  · -- n, m > 1
    cases' hnm with hn hm
    constructor

    · intro hi

      specialize hi (r n) (by sorry) (by sorry)
      cases' hi with k hk
      cases' hk with K' hK'

      let K : ℕ → ℕ := fun l ↦
        if l = 0 then n
        else K' (l - 1)

      use k+1
      use K

      constructor
      · simp [K]
      constructor
      · simp [K]
        exact hK'.right.left
      · intro i hi
        have cases : i = 0 ∨ ¬ i = 0 := by exact Or.symm (ne_or_eq i 0)
        cases' cases with hi' hi'
        · simp [hi', K, hK'.left, rel]

      have aux := lesser_r_finite_steps n m hn hm
      cases' aux with k' hk'

      have aux := frk_lt_fn m k' hk'.left hm
      specialize hi (rPow k' m) hk'.right aux

      cases' hi with k hk
      cases' hk with K hK





      sorry


    · sorry
