import Leantest.Separation.normal



lemma HYPOTHESIS : ∃ f : ℕ → ℚ, f.Bijective ∧ f 0 = 1 ∧ f 1 = 0 := by sorry


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

/-
Lo que he pensado ahora es:
1. realmente no necesito inducción completa??
  porque me vale para cada m < n+1 el G(m) de la G obtenida en el paso n
  (creo)

2. a lo mejor solo tendría que hacerlo para todo n
  tal que cumpla f n ∈ [0, 1]
  y luego debajo y encima del 0 ya pongo empty?? no se

en principio voy a tirar con lo primero a ver
-/

lemma loqueyoquiero {X : Type} [T : TopologicalSpace X]
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
  induction' n with n HI

  · --caso base
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

  · -- caso recursivo
    rw [characterization_of_normal] at hT

    cases' HI with G' hG'

    let G : ℕ → Set X := fun m ↦
      if h : f m < 0 then ∅
      else if h : f m > 1 then Set.univ
      else if h : m < n + 1 then G' m
      else ∅

    use G

    constructor
    · sorry

    · sorry
