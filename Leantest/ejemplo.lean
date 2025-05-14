import Mathlib.Tactic

#check 2

theorem p_and_q (p q : Prop) (hp : p) (hq : q)
    : p ∧ q := by
  constructor
  exact hp
  exact hq
