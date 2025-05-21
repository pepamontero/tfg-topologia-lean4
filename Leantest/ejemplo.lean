import Mathlib.Tactic

#check 2

variable (x : ℕ)
axiom hx : x ≥ 0
#print hx -- ∀ (x : ℕ), x ≥ 0

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩



theorem p_and_q (p q : Prop) (hp : p) (hq : q)
    : p ∧ q := by
  constructor
  exact hp
  exact hq


example : ∀ (p : Prop), p → p := by
  intro p hp
  exact hp

example (p q : Prop) (h : p ∨ q)
  (hpq : p → q) : q := by
  cases' h with hp hq
  · apply hpq
    exact hp
  · exact hq

example : (∃ p : Prop, p) := by
  use True

example (p q : Prop) (hp : p) : p ∨ q := by
  left
  exact hp


example (p q : Prop) (hp : p) (hq : q) :
  p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- exact?

example (p : Prop) : p → p := by
  intro hp
  exact?


example (n : ℕ) : n ≥ 0 := by exact Nat.zero_le n

example (a b c : ℝ) (h : a < b) (hc : c < 0) :
    a + c < b := by exact add_lt_of_lt_of_neg' h hc

