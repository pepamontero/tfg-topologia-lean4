import Leantest.Separation.denumerable
import Leantest.BasicProp.closure

#check decodeRat -- esta es nuestra f : ℕ → ℚ

lemma thislemma
    {X : Type}
    (T : TopologicalSpace X)
    (N : ℕ)
    (P : Finset ℕ)
    (hP : P = {n : ℕ | n < N})

    (G : P → Set X)

    (h1 : ∀ n : P, IsOpen (G n))
    (h2 : ∀ n : P, ∀ m : P, decodeRat n < decodeRat m → Closure (G n) ⊆ G m)

    :
    ∃ U : Set X, (IsOpen U ∧
    (∀ n : P, decodeRat n < decodeRat N → Closure (G n) ⊆ U) ∧
    (∀ n : P, decodeRat N < decodeRat n → Closure U ⊆ G n)) := by

  sorry

variable (X : Type)
variable (T : TopologicalSpace X)

def abierto0 : Set X := ∅
def abierot1 : Set X := ∅

lemma anotherthing
    {X : Type}
    (T : TopologicalSpace X)

    :
    True := by


  let G : ℕ → Set X := fun n ↦
    match n with
    | 0 => ∅
    | n => Set.univ
  sorry
