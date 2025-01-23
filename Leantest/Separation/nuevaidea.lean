import Leantest.Separation.normal



lemma HYPOTHESIS : ∃ f : ℕ → ℚ, f.Bijective ∧ f 0 = 1 ∧ f 1 = 0 := by sorry


lemma thisthing {X : Type} [T : TopologicalSpace X]

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (cond : ℕ → Prop)
    (hcond : cond = fun n ↦
    ∃ G : (Finset.range n) → Set X,
    ( (∀ p : (Finset.range n), IsOpen (G p))
    ∧ (∀ p q : (Finset.range n), p < q → Closure (G p) ⊆ G q) ))

    :

    ∀ n : ℕ, cond n := by

  intro n
  apply Nat.strong_induction_on

  induction' n with n HI

  · --caso base
    sorry

  · --caso recursivo
    sorry

lemma otherthing
    {X : Type} [T : TopologicalSpace X]

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∃ G : ℕ → Set X,
    ( (∀ n : ℕ, IsOpen (G n))
    ∧ (∀ n m : ℕ, n < m → Closure (G n) ⊆ G m) ) := by

  let cond : ℕ → Prop := fun n ↦
      ∃ G : (Finset.range n) → Set X,
      ( (∀ p : (Finset.range n), IsOpen (G p))
      ∧ (∀ p q : (Finset.range n), p < q → Closure (G p) ⊆ G q) )

  have cond_def : ∀ n : ℕ,
  cond n = ∃ G : (Finset.range n) → Set X,
      ( (∀ p : (Finset.range n), IsOpen (G p))
      ∧ (∀ p q : (Finset.range n), p < q → Closure (G p) ⊆ G q) )
  intro n
  rfl

  have h : ∀ n : ℕ, cond n
  intro n
  exact thisthing C1 C2 hC1 hC2 hC1C2 cond (by rfl) n

  have h' : ∀ n : ℕ, ∃ G : (Finset.range n) → Set X,
      ( (∀ p : (Finset.range n), IsOpen (G p))
      ∧ (∀ p q : (Finset.range n), p < q → Closure (G p) ⊆ G q) )
  intro n
  specialize cond_def n
  rw [← cond_def]
  exact h n

  let G : ℕ → Set X := fun n ↦

  sorry

lemma thisthing2 {X : Type} [T : TopologicalSpace X]

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (cond : ℕ × (ℕ → Set X) → Prop)
    (hcond : cond = fun (n, G) ↦ ( (∀ p : (Finset.range n), IsOpen (G p))
    ∧ (∀ p q : (Finset.range n), p < q → Closure (G p) ⊆ G q) ))

    :

    ∀ n : ℕ, (∃ G : ℕ → Set X, cond (n, G)) := by

  intro n

  induction' n with n HI

  · --caso base
    sorry

  · --caso recursivo
    sorry


lemma loqueyoquiero {X : Type} [T : TopologicalSpace X]

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, (
      ∃ G : Finset.range (n + 1) → Set X, (
        (∀ p : Finset.range (n + 1), IsOpen (G p))
        ∧
        (∀ p q : Finset.range (n + 1), p < q → Closure (G p) ⊆ G q)
        )
    ) := by


  intro n

  let motive : ℕ → Prop := fun n ↦
  ∃ G : Finset.range (n + 1) → Set X,
    (∀ p : Finset.range (n + 1), IsOpen (G p)) ∧
    (∀ p q : Finset.range (n + 1), p < q → Closure (G p) ⊆ G q)


  have hn : ∀ n : ℕ, motive n = ∃ G : Finset.range (n + 1) → Set X,
    (∀ p : Finset.range (n + 1), IsOpen (G p)) ∧
    (∀ p q : Finset.range (n + 1), p < q → Closure (G p) ⊆ G q)
  intro n
  rfl

  rw [← hn]

  apply Nat.strongRecOn

  intro n
  induction' n with n HI

  · --caso base
    intro H

    let G : Finset.range 1 → Set X := fun n ↦ C2ᶜ
    use G
    constructor
    · intro p
      simp [G]
      exact { isOpen_compl := hC2 }
    · intro p q hpq
      by_contra

      sorry

  · --caso recursivo
    sorry

noncomputable def f : ℕ → ℚ := Classical.choose HYPOTHESIS

example (n : ℕ) : ∃ r ∈ Finset.range n,
    ((f r < f n) ∧
    (∀ m ∈ Finset.range n, f m < f n → f m ≤ f r)) := by
  induction' n with n HI

  sorry

lemma loqueyoquiero' {X : Type} [T : TopologicalSpace X]
    (hT : NormalTopoSpace T)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, (
      ∃ G : ℕ → Set X, (
        (∀ p : ℕ, p ≤ n → IsOpen (G p))
        ∧
        (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
        )
    ) := by


  intro n

  let motive : ℕ → Prop := fun n ↦
    ∃ G : ℕ → Set X, (
      (∀ p : ℕ, p ≤ n → IsOpen (G p)) ∧
      (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
    )

  have hn : ∀ n : ℕ, motive n =
    ∃ G : ℕ → Set X, (
      (∀ p : ℕ, p ≤ n → IsOpen (G p)) ∧
      (∀ p q : ℕ, p ≤ n → q ≤ n → f p < f q → Closure (G p) ⊆ G q)
    )
  intro n
  rfl

  rw [← hn]

  apply Nat.strongRecOn

  intro n
  induction' n with n HI

  · --caso base
    intro H

    let G : ℕ → Set X := fun n ↦ C2ᶜ
    use G
    constructor
    · intro p hp
      simp [G]
      exact { isOpen_compl := hC2 }

    · intro p q hp hq hpq
      simp at hp hq
      rw [hp, hq] at hpq
      by_contra
      linarith

  · --caso recursivo
    intro hm
    rw [characterization_of_normal] at hT

    simp [hn] at hm

    let G : ℕ → Set X := fun m ↦
      if h : f m < 0 then ∅
      else if h : f m > 1 then Set.univ
      else if h : m < n + 1 then (Classical.choose (hm m h) m)
      else ∅

    use G

    constructor
    · sorry

    · sorry
