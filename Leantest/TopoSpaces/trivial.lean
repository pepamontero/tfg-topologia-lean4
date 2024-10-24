import Mathlib.Tactic

-- ex 1
-- prove that the trivial top. space is in fact a top

open TopologicalSpace

def TrivialTopology (X : Type) : TopologicalSpace X where
  IsOpen (_ : Set X) := true
  isOpen_univ := by
    trivial
  isOpen_inter := by
    intros
    trivial
  isOpen_sUnion := by
    intros
    trivial
