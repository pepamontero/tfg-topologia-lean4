import Mathlib.Tactic

-- meter variables aquí y unificar la notacion

section deptypes

variable (n m : ℚ)
variable (f : ℕ → ℕ)
variable (g : ℕ → ℕ × ℕ)

#check (n, m)

variable (P Q : Prop)
#check P
#check ¬P
#check P ∧ Q



variable (X : Type)
variable (F : Type → Type)

#check fun x : ℕ  ↦ x + 5
#check λ x : ℕ ↦ x + 5

end deptypes


section definitions


def x : ℕ := 2
def X : Type := ℕ




#check X
def Y := ℝ
#check Y

def y := 0
#check y
def z := (0 : ℝ)
#check z

def f : ℕ → ℕ := fun x ↦ x + 5
def g : ℕ → Prop :=  λ x ↦ x = 2

#eval f 4
#eval f x
#eval g 2

end definitions

section paradoja

variable (g c f : Prop)

example (h1 : c ↔ (g ∧ f)) (h2: ¬ f ↔ g ∧ ¬ c) : g ∧ (c ↔ ¬ f) := by
  constructor
  have hf : f ∨ ¬ f
  exact Classical.em f

  cases' hf with hf1 hf2


  sorry
  sorry

end paradoja



-- ejemplo intro_1
example (P Q : Prop) : P → Q := by
  intro hP
  sorry

-- ejemplo intro_2
example (P : X → Prop) : ∀ x : X, P x := by
  intro x
  sorry

-- ejemplos exact
example (P : Prop) : P → P := by
  intro hP
  exact hP

example (A B : Set X)
    (x : X) (hx : x ∈ A ∧ x ∈ B) :
    x ∈ A ∩ B := by
  exact hx

example (A B : Set X)
    (x : X) (h1 : x ∈ A) (h2 : x ∈ B) :
    x ∈ A ∩ B := by
  exact ⟨h1, h2⟩ -- pongo también este ejemplo?? no se

-- ejemplos rfl
example (x : X) : x = x := by
  rfl

example (A B : Set X) (x : X) :
    (x ∈ A ∪ B) ↔ (x ∈ A ∨ x ∈ B) :=
  by rfl

-- ejemplos trivial
example : True := by
  trivial

example (x : X) : x ∈ Set.univ := by
  trivial

-- ejemplos apply
example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ
  exact hP

example (A B : Set X) (h : A ⊆ B) (x : X) (hx : x ∈ A) :
    x ∈ B := by
  apply h
  exact hx

-- ejemplo apply at

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  apply hPQ at hP
  exact hP

-- ejemplos by_contra
example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  by_contra hQ
  apply hPQ at hP
  exact hQ hP

example (h : False) (x y : X) (_: x ≠ y) : x = y := by
  by_contra
  exact h

-- ejemplos left, right

example (P Q : Prop) (h : P) : P ∨ Q := by
  left
  exact h

example (A B : Set X) (h : x ∈ B) : x ∈ A ∪ B := by
  right
  exact h

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

example (A B : Set X) (h : x ∈ A ∩ B) : x ∈ A := by
  exact h.left


-- ejemplos cases'

example (P Q R : Prop) (hPR : P → R) (hQR : Q → R)
    (h : P ∨ Q) : R := by
  cases' h with hP hQ
  · apply hPR
    exact hP
  · apply hQR
    exact hQ

example (P Q : Prop) (h : P ∧ Q) : P := by
  cases' h with hP hQ
  exact hP

-- ejemplos constructor

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (A B : Set X) (h : A = B) : x ∈ A ↔ x ∈ B := by
  constructor
  all_goals rw [h]
  all_goals simp
