import Leantest.Separation.normal
import Leantest.MyDefs.denumerable

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

example (n : ℕ) (hn : n > 1) : FibonacciSet n = {0} ∪ {1} := by
  ext x
  constructor
  all_goals intro hx
  · rw [FibonacciSet.eq_def] at hx
    simp
    sorry
  · simp at hx

    induction' hn with n HI
    · -- CB
      simp
      rw [FibonacciSet.eq_def]
      cases' hx with hx hx
      · right
        rw [FibonacciSet.eq_def]
        simp
        exact hx
      · left
        rw [FibonacciSet.eq_def]
        simp
        exact hx

    · -- CR

      cases' hx with hx hx
      · rw [hx]
        simp

        sorry
      · sorry

/- ejemplos

variable (X : Type)
variable (T : TopologicalSpace X)
variable (C1 C2 : Set X)

def F : ℕ → Set X := fun n ↦
  match n with
  | 0 => C1
  | 1 => C2
  | n + 2 => F n ∪ F (n + 1)


def G (Y : Type) (TY : TopologicalSpace Y)
    (A B : Set Y) : ℕ → Set Y := fun n ↦
  match n with
  | 0 => A
  | 1 => B
  | n + 2 => G Y TY A B n ∪ G Y TY A B (n + 1)

-/



def f := decodeRat

lemma rProp (n : ℕ) : ∃ r : ℕ,  ( (f r < f n) ∧
  (∀ m : ℕ, (m < n ∧ m ≠ r) → f m < f r) ∧
  (r < n) ) := by
  sorry

lemma sProp (n : ℕ) : ∃ s : ℕ, ( (f n < f s) ∧
  (∀ m : ℕ, (m < n ∧ m ≠ s) → f s < f m) ∧
  (s < n) ) := by
  sorry

noncomputable def r : ℕ → ℕ := fun n ↦
  match n with
  | 0 => 0
  | n => Classical.choose (rProp n)
-- realmente lo que quiero que haga es que dado n, me devuelve un r en {0, 1, ..., n-1} tal que f s < f n y sea la mejor elección. análogo para s

lemma rn_lt_n (n : ℕ) (hn : n > 0) : r n < n := by
  rw [r]
  let h := Classical.choose_spec (rProp n)
  exact h.right.right
  intro hn0
  linarith

noncomputable def s : ℕ → ℕ := fun n ↦ Classical.choose (sProp n)

lemma sn_lt_n (n : ℕ) : s n < n := by
  let h := Classical.choose_spec (sProp n)
  exact h.right.right

/- idea: le quito las hipótesis al hT y las meto ddespués?
def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X :=

    fun n ↦
  match n with
  | 0 => C2ᶜ
  | 1 => Classical.choose (hT C2ᶜ C1)
  | n => Classical.choose (hT (G hT C1 C2 hC1 hC2 hC1C2 (r n)) (G hT C1 C2 hC1 hC2 hC1C2 (s n)))
  decreasing_by
  · exact (sn_lt_n n)
  · exact (rn_lt_n n)
-/




--esta es la buena
def G {X : Type} [T : TopologicalSpace X]
    (hT : ∀ (U C : Set X), IsOpen U → IsClosed C → C ⊆ U → ∃ V, IsOpen V ∧ C ⊆ V ∧ Closure V ⊆ U)
    (C1 C2 : Set X)
    (hC1 : IsClosed C1)
    (hC2 : IsOpen C2ᶜ)
    (hC1C2 : C1 ⊆ C2ᶜ)

    : ℕ → Set X :=

    fun n ↦
  let F : ℕ → Set X := fun n ↦
  if n = 0 then C2ᶜ
  else if n = 1 then Classical.choose (hT C2ᶜ C1 hC2 hC1 hC1C2)
  else G hT C1 C2 hC1 hC2 hC1C2 n

  match n with
  | 0 => F 0
  | 1 => F 1
  | n => Classical.choose (hT (F (r n)) (Closure (F (s n)))

  (by
  · have cases : r n = 0 ∨ r n > 0
    exact Nat.eq_zero_or_pos (r n)
    cases' cases with h0 hn

    · -- r n = 0
      rw [h0]
      dsimp [F]
      exact hC2

    have cases : r n = 1 ∨ r n > 1
    exact LE.le.eq_or_gt hn
    cases' cases with h1 hn

    · -- r n = 1
      rw [h1]
      dsimp [F]
      let h := Classical.choose_spec (hT C2ᶜ C1 hC2 hC1 hC1C2)
      exact h.left

    · -- r n > 1
      have hF : F (r n) = G hT C1 C2 hC1 hC2 hC1C2 n
      dsimp [F]
      sorry

      rw [hF]






    have h' : G hT C1 C2 hC1 hC2 hC1C2 0 = C2ᶜ
    sorry
    sorry


    induction' n
    · rw [r]
      have h0 : G hT C1 C2 hC1 hC2 hC1C2 0 = C2ᶜ
      sorry -- es que esto es por definición ...
      rw [h0]
      exact hC2

    ·
      sorry)

  (by sorry)

  (by sorry))

  decreasing_by
  · exact (sn_lt_n n)
  · exact (rn_lt_n n (by sorry)) -- es como trivial????? q n no es ni 0 ni 1
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry -- no se por que se me crean mas goals


#check decodeRat
#check decodeRatProp


/- en construcción
lemma idk1 (n : ℕ) : ∃ r : ℕ,  ( (decodeRat (r) < decodeRat n) ∧
  (∀ m : ℕ, m < n → decodeRat m < decodeRat (r)) ∧
  (r < n) ) := by

  let P : Finset ℕ := Finset.range n

  let R : Finset ℕ := P.filter (fun r ↦ (decodeRat r < decodeRat n))

  let S : Finset ℕ := P.filter (fun p ↦ f p > f n)

  sorry

-/



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

  /- pruebas

  let FibonacciSet : ℕ → Set ℕ := fun n ↦
    match n with
    | 0 => {0}
    | 1 => {1}
    | n + 2 => FibonacciSet n ∪ FibonacciSet (n + 1)

  let G : ℕ → Set X := fun n ↦
    match n with
    | 0 => C1
    | 1 => C2
    | n + 2 => G n ∪ G (n + 1)

  let G : ℕ → Set X := fun n ↦
    match n with
    | 0 => C2ᶜ
    | 1 => Classical.choose (hT C2ᶜ C1 aux hC1' aux')
    | n + 2 => Classical.choose (hT (Closure G (r n)) (G (s n)))
  -/


  -- efectivamente es un problema deque tiene que ser def y no let... fuck

  sorry
