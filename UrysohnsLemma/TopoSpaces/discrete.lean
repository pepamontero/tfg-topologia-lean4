import Mathlib.Tactic

-- ex 1
-- prove that the trivial top. space is in fact a top

open TopologicalSpace

-- ANCHOR: DiscreteTopo
@[reducible]
-- ANCHOR: DiscreteTopo_isOpen_field
def DiscreteTopo (X : Type) : TopologicalSpace X where
  IsOpen (_ : Set X) := true
-- ANCHOR_END: DiscreteTopo_isOpen_field
-- ANCHOR: DiscreteTopo_isOpen_univ_partial
  isOpen_univ := by
-- ANCHOR_END: DiscreteTopo_isOpen_univ_partial
    trivial
  isOpen_inter := by
    intros
    trivial
  isOpen_sUnion := by
    intros
    trivial
-- ANCHOR_END: DiscreteTopo
