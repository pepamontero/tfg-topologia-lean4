import Mathlib.Tactic

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
    use G (f (s)

    constructor
    · exact hP1 s hs
    · intro t ht1 ht2
      exact hP2 t ht1 s hs ht2


  sorry
