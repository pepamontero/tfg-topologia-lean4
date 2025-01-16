import Mathlib.Tactic
import Leantest.Separation.normal


-- primera idea
example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)
    (P : Finset ℕ)
    (h0 : 0 ∈ P)
    (h1 : 1 ∈ P)
    (k : ℕ) (hk : k = P.card)
    (G : ℚ → Set X)
    (f : ℕ → ℚ)
    (hP1 : ∀ n ∈ P, IsOpen (G (f n)))
    (hP2 : ∀ n ∈ P, ∀ m ∈ P, f n < f m → Closure (G (f n)) ⊆ G (f m))
    (s : ℕ)
    :
    (∃ U : Set X, (IsOpen U) ∧
    (∀ t ∈ P, (f t < f s → Closure (G (f t)) ⊆ U))) := by

induction' s with s HI

· -- CB
  use G (f 0)

  constructor
  · exact hP1 0 h0
  · intro t ht1 ht2
    exact hP2 t ht1 0 h0 ht2

· -- CR

  have options : s ∈ P ∨ s ∉ P
  exact Decidable.em (s ∈ P)

  cases' options with hs hs

  · -- if s ∈ P, trivial
    use G (f (s))

    constructor
    · exact hP1 s hs
    · intro t ht1 ht2
      sorry
  sorry



-- segunda idea


example {X : Type}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsClosed C2)

    (G : ℚ → Set X)
    (f : ℕ → ℚ)

    (hf0 : f 0 = 1)
    (hf1 : f 1 = 0)

    (hf : ∀ n : ℕ, 0 ≤ f n ∧ f n ≤ 1)
    (finy : f.Injective)

    (P : Finset ℕ)

    (hP : { n : ℕ | IsOpen (G (f n)) ∧
    (∀ m ∈ P, f n < f m → Closure (G (f n)) ⊆ G (f m)) })


    (h0 : 0 ∈ P)
    (h1 : 1 ∈ P)

    --(k : ℕ) (hk : k = P.card)

    (s : ℕ)

    :

    s ∈ P := by

  apply Nat.strong_induction_on
  intro n hn

  /-
  paso 1. Quiero ver que n no es 0 ni 1
  (seguramente hay formas más fáciles de hacerlo)
  -/

  have aux : n = 0 ∨ n > 0
  exact Nat.eq_zero_or_pos n
  cases' aux with hn' hn'

  · -- n=0
    rw [hn']
    exact h0

  · have aux : n = 1 ∨ n > 1
    exact LE.le.eq_or_gt hn'
    cases' aux with hn' hn'

    · -- n=1
      rw [hn']
      exact h1

    · -- n not 0 or 1

  /-
  paso 2. si n no es 0 ni 1,
  entonces f n no es 0 ni 1 (f inyectiva)
  entonces puedo encontrar t,s en P tal que
  f t < f n < f s
  -/

      let S : Finset ℕ := P.filter (fun p ↦ f p > f n)
      -- nota: esto no son filtros jaja

      have H : S.Nonempty
      use 0
      rw [Finset.mem_filter]
      constructor
      · exact h0
      · rw [hf0]
        specialize hf n
        cases' hf with _ hf
        apply Ne.lt_of_le
        rw [← hf0]
        by_contra c
        apply finy at c
        linarith
        exact hf

      let s : ℕ := Finset.min' S H

      let I : Finset ℕ := P.filter (fun p ↦ f p < f n)
      -- nota: esto no son filtros jaja

      have H : I.Nonempty
      use 1
      rw [Finset.mem_filter]
      constructor
      · exact h1
      · rw [hf1]
        specialize hf n
        cases' hf with hf _
        apply Ne.lt_of_le
        rw [← hf1]
        by_contra c
        apply finy at c
        linarith
        exact hf

      let i : ℕ := Finset.max' I H









      have hS : S ⊆ P
      intro x hx
      simp [Sdef] at hx
      exact hx.left

      have hS : Finset S
      exact Finset.subtype (fun x ↦ x ∈ S) P

      let s : ℕ := Min S'



      have aux : f n ≠ 0
      by_contra c
      rw [← hf1] at c
      apply finy at c
      linarith

      have aux' : f n ≠ 1
      by_contra c
      rw [← hf0] at c
      apply finy at c
      linarith

      have hn1 : ∃ t ∈ P, f t < f n
      use 1
      constructor
      · exact h1
      · rw [hf1]
        specialize hf n
        exact lt_of_le_of_ne hf.left (id (Ne.symm aux))


      have hn2 : ∃ s ∈ P, f n < f s
      use 0
      constructor
      · exact h0
      · rw [hf0]
        specialize hf n
        exact lt_of_le_of_ne hf.right aux'




      sorry
