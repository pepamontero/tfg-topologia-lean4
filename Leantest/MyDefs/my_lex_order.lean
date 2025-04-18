import Mathlib.Tactic


def lt_pair : (ℕ × ℕ) → (ℕ × ℕ) → Prop := Prod.Lex (Nat.lt) (Nat.lt)
def lt_pair_wfr : WellFoundedRelation (ℕ × ℕ) := Prod.lex (Nat.lt_wfRel) (Nat.lt_wfRel)
lemma lt_pair_wf : WellFounded lt_pair := lt_pair_wfr.wf



lemma lt_pair_def (n m i j : ℕ)
    : lt_pair (n, m) (i, j) ↔ n < i ∨ (n = i ∧ m < j):= by
  constructor

  · intro h

    have cases : n < i ∨ i ≤ n := by exact Nat.lt_or_ge n i
    cases' cases with hni hni

    · -- n < i
      left
      exact hni

    have cases : i < n ∨ i = n := by exact Or.symm (Nat.eq_or_lt_of_le hni)
    cases' cases with hni hni

    · -- i < n
      apply (@Prod.Lex.left ℕ ℕ Nat.lt Nat.lt i j n m) at hni
      apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at hni
      by_contra
      exact hni h

    · -- i = n
      simp [hni]

      have cases : m < j ∨ j ≤ m := by exact Nat.lt_or_ge m j
      cases' cases with hmj hmj

      · -- m < j
        exact hmj

      have cases : j < m ∨ j = m := by exact Or.symm (Nat.eq_or_lt_of_le hmj)
      cases' cases with hmj hmj

      · -- j < m
        rw [hni] at h

        apply (@Prod.Lex.right ℕ ℕ Nat.lt Nat.lt n) at hmj
        apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at hmj
        by_contra
        exact hmj h

      · -- j = m
        rw [hni, hmj] at h
        by_contra
        have h' := h
        apply @WellFoundedRelation.asymmetric (ℕ × ℕ) lt_pair_wfr at h'
        exact h' h

  · intro h
    cases' h with h h
    · apply Prod.Lex.left
      exact h
    · rw [h.left]
      apply Prod.Lex.right
      exact h.right
