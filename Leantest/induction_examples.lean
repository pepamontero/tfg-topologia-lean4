import Mathlib.Tactic


-- NOTA: `∑ i in Finset.range n` toma valores de `i` de `0` a `n-1` (incluidos)

-- lo siguiente lo solemos usar en inducción:
example  (n : ℕ) (f : ℕ → ℝ): ∑ i in Finset.range (n + 1), f i =
    (∑ i in Finset.range n, f i) + f n := by

  exact Finset.sum_range_succ f n --exact?


-- Introduction to induction
example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  -- induction on `n`.
  induction' n with n HI

  -- CB
  simp

  -- CR
  simp
  rw [Finset.sum_range_succ]
  rw [HI]
  ring

example (a b c : ℝ) (hc : c > 0) : a ≥ b ↔ a*c ≥ b*c := by
  exact Iff.symm (mul_le_mul_iff_of_pos_right hc)

-- Induction over restrictions
example (n : ℕ) (hn : n > 2) : 2^n ≥ n + 5 := by
  induction' hn with n hn HI

  · simp

  · simp at *
    ring_nf
    trans (n + 5) * 2
    · linarith
    · simp
      exact HI



--Induction over 2 variables
example (n m : ℕ) (f : (ℕ × ℕ) → ℕ)
    (hn : n > 0)
    (hm : m > 0)
    (h1 : ∀ n : ℕ, f (1, n) = n)
    (h2 : ∀ m : ℕ, f (m, 1) = m)
    (h3 : ∀ n m : ℕ, f (m, n) = f (m-1, n) + f (m, n-1) - f (m-1, n-1)) :
    f (m, n) = m + n - 1 := by



  induction' hn with n hn IHn generalizing m
  · simp
    exact h2 m

  · induction' hm with m hm IHm
    · simp
      exact h1 (n + 1)

    · simp at *
      rw [h3]
      simp
      -- `generalizing m` is neccessary for following step:
      rw [IHm, IHn m (by linarith), IHn (m+1) (by linarith)]
      -- otherwise we can't sort of specialize IHn
      simp
      sorry -- faltan solo cuentas
