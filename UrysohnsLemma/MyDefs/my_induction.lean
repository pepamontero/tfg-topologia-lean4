import Mathlib.Tactic

#check Nat.strong_induction_on

-- ANCHOR: my_stronger_induction_sig
theorem my_stronger_induction (n : ℕ) (P Q : ℕ → Prop)
    (hn : P n)
    (h : ∀ n : ℕ, P n → ((∀ m < n, P m → Q m) → Q n)) :
    (Q n) := by
-- ANCHOR_END: my_stronger_induction_sig

  have aux : ∀ k : ℕ, P k → ((P k → Q k) ↔ Q k)
  intro k hk
  constructor
  · exact fun a ↦ a hk
  · exact fun a _ ↦ a

  rw [← aux n hn]

  let H : ℕ → Prop := fun k ↦ (P k → Q k)
  have H_def : ∀ k : ℕ, H k = (P k → Q k) := by intro k; rfl

  rw [← H_def n]

  apply Nat.strong_induction_on
  intro k hi

  simp [H]
  intro hk
  specialize h k hk
  apply h
  intro m hm
  specialize hi m hm
  simp [H] at hi
  exact hi


-- a ver necesito entender esto
theorem my_induction (n : ℕ) (P : ℕ → Prop)
    (h0 : P 0)
    (hi : ∀ n, P n → P (n+1)) : P n := by
  induction' n with n hn
  · exact h0
  · apply hi n
    exact hn

theorem my_double_induction (n m : ℕ) (P : ℕ → ℕ → Prop)
    (h0 : P 0 0)
    (hi : ∀ n m, ((P n m → P (n+1) m) ∧ (P n m → P n (m+1)))) : P n m := by
  induction' n with n hn
  · induction' m with m hm
    · exact h0
    · apply (hi 0 m).right
      exact hm
  · apply (hi n m).left
    exact hn

theorem my_double_induction' (n m : ℕ) (P : ℕ → ℕ → Prop)
    (h0 : P 0 0)
    (hi : ∀ n m, (P n m → (P (n+1) m  ∧ P n (m+1)))) : P n m := by
  induction' n with n hn
  · induction' m with m hm
    · exact h0
    · specialize hi 0 m hm
      exact hi.right
  · specialize hi n m hn
    exact hi.left


theorem my_strong_induction (n : ℕ) (P : ℕ → Prop)
    (hi : ∀ n, (∀ k < n, P k) → P n) : P n := by

  -- la idea es encontrar un Q tal que se base en probar Q n por inducción normal
  let Q : ℕ → Prop := fun n ↦ ∀ k ≤ n, P k
  have hQ : Q n → P n
  · simp [Q]
    intro h
    exact h n (by linarith)

  apply hQ
  apply my_induction n Q

  · -- caso base
    simp [Q]
    apply hi
    intro k hk
    simp at hk

  · -- caso recursivo
    intro n hn
    simp [Q] at *
    intro k hk
    have cases : k < n + 1 ∨ k = n + 1 := by exact Or.symm (Nat.eq_or_lt_of_le hk)
    cases' cases with hk hk
    · exact hn k (by linarith)
    · rw [hk]
      apply hi (n+1)
      intro l hl
      exact hn l (by linarith)



theorem my_strong_double_induction (n m : ℕ) (P : ℕ → ℕ → Prop)
    (hi : ∀ n m, ((∀ k < n, P k m) → P n m) ∧ ((∀ l < m, P n l) → P n m)) : P n m := by

  let Q : ℕ → ℕ → Prop := fun n ↦ fun m ↦ ∀ k ≤ n, ∀ l ≤ m, P k l
  have hQ : Q n m → P n m
  · intro hQ
    simp [Q] at hQ
    exact hQ n (by linarith) m (by linarith)

  apply hQ
  apply my_double_induction

  · -- caso base
    intro n hn m hm
    specialize hi 0 0
    cases' hi with hil hir
    simp at hn hm
    rw [hn, hm]
    apply hil
    simp

  · -- caso recursivo
    intro n m
    simp [Q] at *
    constructor

    · intro hi' k hk l hl
      have cases : k < n + 1 ∨ k = n + 1 := by exact Or.symm (Nat.eq_or_lt_of_le hk)
      cases' cases with hk hk

      · exact hi' k (by linarith) l hl
      · rw [hk]
        specialize hi (n+1) l
        cases' hi with hi _
        apply hi
        intro k hk
        exact hi' k (by linarith) l hl

    · intro hi' k hk l hl
      have cases : l < m + 1 ∨ l = m + 1 := by exact Or.symm (Nat.eq_or_lt_of_le hl)
      cases' cases with hl hl

      · exact hi' k hk l (by linarith)
      · rw [hl]
        specialize hi k (m+1)
        cases' hi with _ hi
        apply hi
        intro l hl
        exact hi' k hk l (by linarith)


theorem my_strong_double_induction' (n m : ℕ) (P : ℕ → ℕ → Prop)
    (hi : ∀ n m, ((∀ i < n, ∀ j < m, P i j) → P n m)) : P n m := by

  let Q : ℕ → ℕ → Prop := fun n ↦ fun m ↦ ∀ k ≤ n, ∀ l ≤ m, P k l
  have hQ : Q n m → P n m
  · intro hQ
    simp [Q] at hQ
    exact hQ n (by linarith) m (by linarith)

  apply hQ
  apply my_double_induction

  · -- caso base
    intro n hn m hm
    specialize hi 0 0
    simp at hn hm
    rw [hn, hm]
    apply hi
    simp

  · -- caso recursivo
    intro n m
    simp [Q] at *
    constructor

    · intro hi' k hk l hl
      have cases : k < n + 1 ∨ k = n + 1 := by exact Or.symm (Nat.eq_or_lt_of_le hk)
      cases' cases with hk hk

      · exact hi' k (by linarith) l hl
      · rw [hk]
        specialize hi (n+1) l
        apply hi
        intro i hin j hj
        exact hi' i (by linarith) j (by linarith)

    · intro hi' k hk l hl
      have cases : l < m + 1 ∨ l = m + 1 := by exact Or.symm (Nat.eq_or_lt_of_le hl)
      cases' cases with hl hl

      · exact hi' k hk l (by linarith)
      · rw [hl]
        specialize hi k (m+1)
        apply hi
        intro i hik j hj
        exact hi' i (by linarith) j (by linarith)


-- repito este resultado solo por tenerlo aquí visible
theorem my_stronger_induction' (n : ℕ) (P Q : ℕ → Prop)
    (hn : P n)
    (h : ∀ n : ℕ, P n → ((∀ m < n, P m → Q m) → Q n)) :
    (Q n) := by

  have aux : ∀ k : ℕ, P k → ((P k → Q k) ↔ Q k)
  · intro k hk
    constructor
    · exact fun a ↦ a hk
    · exact fun a _ ↦ a

  rw [← aux n hn]

  let H : ℕ → Prop := fun k ↦ (P k → Q k)
  have H_def : ∀ k : ℕ, H k = (P k → Q k) := by intro k; rfl

  rw [← H_def n]

  apply my_strong_induction
  intro k hi

  simp [H]
  intro hk
  specialize h k hk
  apply h
  intro m hm
  specialize hi m hm
  simp [H] at hi
  exact hi


theorem my_stronger_double_induction (n m : ℕ) (P Q : ℕ → ℕ → Prop)
    (hnm : P n m)
    (h : ∀ n m, P n m →
      ((∀ k < n, P k m → Q k m) → Q n m)
      ∧
      ((∀ l < m, P n l → Q n l) → Q n m)
    ) :
    Q n m := by

  have aux : ∀ k l, P k l → ((P k l → Q k l) ↔ Q k l)
  · intro k l hkl
    constructor
    · exact fun a ↦ a hkl
    · exact fun a _ ↦ a

  rw [← aux n m hnm]

  let H : ℕ → ℕ → Prop := fun k ↦ fun l ↦ (P k l → Q k l)
  have H_def : ∀ k l : ℕ, H k l = (P k l → Q k l) := by intro k l; rfl

  rw [← H_def n m]

  apply my_strong_double_induction
  intro k l

  simp [H]
  constructor

  · intro hi hkl
    specialize h k l hkl
    cases' h with h _
    apply h
    exact hi

  · intro hi hkl
    specialize h k l hkl
    cases' h with _ h
    apply h
    exact hi
