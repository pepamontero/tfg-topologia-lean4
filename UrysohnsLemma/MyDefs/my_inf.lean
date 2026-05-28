import Mathlib.Tactic

def isMyLowerBound (x : ℝ) (A : Set ℚ) : Prop :=
  ∀ y : ℚ, y ∈ A → x ≤ y

def isMyInf (x : ℝ) (A : Set ℚ) : Prop :=
  /-
  x es infimo de A si cumple:
  - x es cota inferior
  - si y es cota inferior → y ≤ x
  -/
  isMyLowerBound x A ∧ (∀ y : ℝ, (isMyLowerBound y A → y ≤ x))

def hasMyInf (A : Set ℚ) : Prop :=
  ∃ x : ℝ, isMyInf x A

noncomputable def MyInf (A : Set ℚ) (hA : hasMyInf A) : ℝ := Classical.choose hA

def hasMyMin (A : Set ℚ) : Prop :=
  ∃ p ∈ A, ∀ q ∈ A, p ≤ q

noncomputable def MyMin (A : Set ℚ) (hA : hasMyMin A) : ℚ := Classical.choose hA

lemma min_implies_inf (A : Set ℚ) : hasMyMin A → hasMyInf A := by
  intro h
  cases' h with p hp
  use p
  constructor
  · rw [isMyLowerBound]
    simp
    exact hp.right
  · intro y
    rw [isMyLowerBound]
    intro ha
    specialize ha p hp.left
    exact ha

lemma inf_is_unique (x y : ℝ) (A : Set ℚ)
    (hx : isMyInf x A)
    (hy : isMyInf y A) : x = y := by

  rw [isMyInf] at *
  cases' hx with hx1 hx2
  cases' hy with hy1 hy2
  specialize hx2 y hy1
  specialize hy2 x hx1
  linarith
