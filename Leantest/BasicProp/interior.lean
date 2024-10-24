import Mathlib.Tactic
import Leantest.TopoSpaces.trivial

-- ex 1
-- prove that the discrete top. space is in fact a top

open TopologicalSpace

#check interior



example : interior (Set.Icc 1 2) = Set.Ioo 1 2 := by
  rw [Set.Icc]
  rw [Set.Ioo]
  rw [interior]
  ext x
  constructor <;> intro hx
  · simp
    simp at hx
    cases' hx with t ht
    sorry
  · simp
    simp at hx
    use Set.Ioo 1 2
    constructor
    · linarith
    · exact hx
