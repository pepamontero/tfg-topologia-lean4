import Leantest.Separation.normal
import Leantest.Separation.denumerable


#check Closure

/-
Practice on recursive definitions
-/

def Fibonacci : ℕ → ℕ := fun n ↦
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Fibonacci n + Fibonacci (n + 1)


def FibonacciSet : ℕ → Set ℕ := fun n ↦
  match n with
  | 0 => {0}
  | 1 => {1}
  | n + 2 => FibonacciSet n ∪ FibonacciSet (n + 1)


variable (X : Type)
variable (T : TopologicalSpace T)
variable (C1 C2 : Set X)


def F : ℕ → Set X := fun n ↦
  match n with
  | 0 => C1
  | 1 => C2
  | n + 2 => F n ∪ F (n + 1)

#check decodeRat
#check decodeRatProp

def Q : ℕ → ℚ := fun n ↦ Classical.choose (decodeRatProp n n.property)


lemma idk1 (n : ℕ) : ∃ r : ℕ,  ( (decodeRat (r) < decodeRat n) ∧
  (∀ m : ℕ, m < n → decodeRat m < decodeRat (r)) ∧
  (r < n) ) := by

  let P : Finset ℕ := Finset.range n

  let R : Finset ℕ := P.filter (fun r ↦ (decodeRat r < decodeRat n))

  let S : Finset ℕ := P.filter (fun p ↦ f p > f n)

  sorry


lemma idk  {X : Type} {Y : Set ℝ}
    (T : TopologicalSpace X)
    (hT : NormalTopoSpace T)

    (C1 C2 : Set X)
    (hC1 : C1 ≠ ∅)
    (hC2 : C2 ≠ ∅)
    (hC1' : IsClosed C1)
    (hC2' : IsClosed C2)
    (hC1C2 : C1 ∩ C2 = ∅)

    (h1 : decodeRat 1 = some 0)
    (h0 : decodeRat 0 = some 1) -- esto tendré que ver como lo apaño
    :
    ∃ G : ℕ → Set X, ((∀ n : ℕ, IsOpen (G n)) ∧
    (∀ n m : ℕ, decodeRat n < decodeRat m → Closure (G n) ⊆ G m)) := by


  /-
  have hr : ∃ r : ℕ × (Set ℕ) → ℕ, ∀ n : ℕ, ∀ P : Set ℕ, ∀ m : ℕ, m < n →
  decodeRat (r (n, P)) < decodeRat m
  sorry

  have hs : ∃ s : ℕ × (Set ℕ) → ℕ, ∀ n : ℕ, ∀ P : Set ℕ, ∀ m : ℕ, m < n →
  decodeRat m < decodeRat (s (n, P))
  sorry
  -/ -- lo repito

  have hr : ∃ r : ℕ → ℕ, ∀ n : ℕ, ( (decodeRat (r n) < decodeRat n) ∧
  (∀ m : ℕ, m < n → decodeRat m < decodeRat (r n)) ∧
  (r n < n) )
  sorry

  have hs : ∃ s : ℕ → ℕ, ∀ n : ℕ, ( (decodeRat n < decodeRat (s n)) ∧
  (∀ m : ℕ, m < n → decodeRat (s n) < decodeRat m) ∧
  (s n < n) )
  sorry

  cases' hr with r hr
  cases' hs with s hs

  rw [characterization_of_normal] at hT

  have aux : IsOpen C2ᶜ
  exact IsClosed.isOpen_compl

  have aux' : C1 ⊆ C2ᶜ
  exact ABdisjoint_iff_AsubsBc.mp hC1C2

  let FibonacciSet : ℕ → Set ℕ := fun n ↦
    match n with
    | 0 => {0}
    | 1 => {1}
    | n + 2 => FibonacciSet n ∪ FibonacciSet (n + 1)

  let G : ℕ → Set X := fun n ↦
    match n with
    | 0 => C2ᶜ
    | 1 => Classical.choose (hT C2ᶜ C1 aux hC1' aux')
    | n + 2 => Classical.choose (hT (Closure G (r n)) (G (s n)) ? ? ?)



  -- efectivamente es un problema deque tiene que ser def y no let... fuck


  use G
  sorry
