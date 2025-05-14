import Mathlib.Tactic

#check Nat







-- meter variables aquí y unificar la notacion

#print True

axiom A : Prop
axiom h : A → A
axiom a : ℕ
axiom ha : a > 2

variable (x : ℕ)
axiom hx : x ≥ 0
#check hx

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := sorry


def mi_proposicion : Prop := False → True

def prueba_de_mi_proposicion : mi_proposicion := by intro h; by_contra; exact h

def my_comm_sum (a b : ℕ) : a + b = b + a := by exact Nat.add_comm a b

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

end definitions


section resultados

  example : 2 + 2 = 4 := by sorry

lemma my_obvious_lemma (P : Prop) (h : P) : P := by sorry

theorem modus_ponens (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by sorry

end resultados



section tacticas_basicas

/-
INTRO
-/

example (P Q : Prop) : P → Q := by
  intro hP
  sorry

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

example : P := by
  by_contra h
  sorry

example (P Q : Prop) (hPQ : P → Q) (hP : P) : Q := by
  by_contra hQ
  apply hPQ at hP
  exact hQ hP

example (h : False) (x y : X) (_: x ≠ y) : x = y := by
  by_contra
  exact h

example (h : x ∈ (∅ : Set X)) : 1 = 2 := by
  by_contra
  exact h

end tacticas_basicas


section otros_resultados

/-
  EJEMPLO EXACT O APPLY UTILIZANDO OTROS RESULTADOS
-/

lemma lemma_exact (n : ℕ) : 2^n > 0 := by
  exact Nat.two_pow_pos n

#check Nat.two_pow_pos

example : 2^5 > 0 := by
  exact lemma_exact 5

lemma lemma_apply (n : ℕ) : n ≥ 2 → 2^n > n := by sorry

example : 2^5 > 5 := by
  apply lemma_apply 5
  sorry

def es_par (n : ℕ) : Prop := ∃ m : ℕ, n = 2 * m

example : es_par 2 := by sorry


end otros_resultados

section simplificaciones

-- rw

example (a b : ℕ) (h : a = b) : es_par (a + b) := by
  rw [h]
  rw [es_par]

example : 1 + 1 = 2 := by simp
example : 1 + 1 = 2 := by ring


end simplificaciones



section conectores_logicos



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





end tacticas
