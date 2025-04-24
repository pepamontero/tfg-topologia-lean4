
import Leantest.Separation.normal
import Leantest.MyDefs.my_induction
import Leantest.MyDefs.my_rs_functions

---- LO QUE MOLARÍA TENER

lemma would_be_cool {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :
      ∃ G : ℕ → Set X, (
        (G 0 = C2ᶜ)
        ∧
        (G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
        ∧
        (∀ n, IsOpen (G n))
        ∧
        (∀ n > 1, (Closure (G (r n)) ⊆ G n ∧ Closure (G n) ⊆ G (s n)))
        )
    := by
  sorry

noncomputable def G_cool {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X := Classical.choose (would_be_cool hT C1 C2 hC1 hC2 hC1C2)

lemma cool_prop1 {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    ∀ n : ℕ, IsOpen (G_cool hT C1 C2 hC1 hC2 hC1C2 n) := by

  intro n
  simp [G_cool]
  exact (Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.left n

lemma cool_prop2a {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n > 1, Closure (G (r n)) ⊆ G n:= by

  intro G n hn
  simp [G, G_cool]
  exact ((Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.right n hn).left

lemma cool_prop2b {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n > 1, Closure (G n) ⊆ G (s n):= by

  intro G n hn
  simp [G, G_cool]
  exact ((Classical.choose_spec (would_be_cool hT C1 C2 hC1 hC2 hC1C2)).right.right.right n hn).right

lemma cool_inference {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    :

    let G := G_cool hT C1 C2 hC1 hC2 hC1C2

    ∀ n m : ℕ, f n < f m → Closure (G n) ⊆ G m := by

  intro G n m hmn

  cases' n with n

  · -- n = 0
    cases' m with m
    · -- m = 0
      by_contra
      exact (lt_self_iff_false (f 0)).mp hmn

    cases' m with m
    · -- m = 1
      by_contra
      simp [f_prop.right.left, f_prop.right.right] at hmn
      exact (Bool.eq_not_self ((1).blt ↑0)).mp hmn

    · -- m > 1
      simp [G, G_cool]
      sorry


  · sorry
