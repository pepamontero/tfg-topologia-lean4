import Leantest.Separation.normal
import Leantest.MyDefs.my_induction
import Leantest.MyDefs.my_rs_functions

lemma aux (n m : ℕ) (hn1 : n > 1) (hm1 : m > 1)
    (hfnm : f n < f m) :
  f (s n) ≤ f m ∨ f n ≤ f (r m) := by
  sorry


lemma something {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)

    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    (G : ℕ → Set X)
    (hG0 : G 0 = C2ᶜ)
    (hG1 : G 1 = Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2))
    (hGOpen : ∀ n, IsOpen (G n))
    (hG: ∀ n > 1,
        (Closure (G (r n)) ⊆ G n) ∧
        (Closure (G n) ⊆ G (s n))
    )

    :

    ∀ n, ∀ m, n > 1 → m > 1 → f n < f m → Closure (G n) ⊆ G m
     := by

  intro n m hn1 hm1 hfnm

  let P : ℕ → ℕ → Prop := fun i ↦ fun j ↦ (i > 1) ∧ (j > 1) ∧ (f i < f j)
  have hP : P n m := by constructor; exact hn1; constructor; exact hm1; exact hfnm

  let Q : ℕ → ℕ → Prop := fun i ↦ fun j ↦ Closure (G i) ⊆ G j

  apply my_stronger_double_induction' n m P Q hP
  simp [P, Q]

  intro n m hn1 hm1 hfnm HI

  have aux := aux n m hn1 hm1 hfnm
  cases' aux with aux1 aux2

  · have cases := Or.symm (Decidable.lt_or_eq_of_le aux1)
    cases' cases with h h
    · sorry -- trivial

    ·
    sorry
