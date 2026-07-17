import Mathlib.Tactic
import UrysohnsLemma.TopoSpaces.usual

-- Proposed restatements from the thesis's "Posibles mejoras y ampliaciones"
-- section (chapter 5), shown as signatures only (not yet proved in this form
-- in the main development, which uses its own topology/normality
-- definitions instead of the Mathlib ones used here).

-- ANCHOR: urysohn_mathlib_statement
theorem Urysohn {X : Type} [T : TopologicalSpace X]
    [N : NormalSpace X] {s t : Set X} (hs : IsClosed s)
    (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : X → ℝ, Continuous f ∧ Set.EqOn f 0 s ∧ Set.EqOn f 1 t
      ∧ ∀ x, f x ∈ Set.Icc 0 1 := by
  sorry
-- ANCHOR_END: urysohn_mathlib_statement

-- ANCHOR: my_usual_equiv_statement
lemma my_usual_equiv : @UniformSpace.toTopologicalSpace ℝ
    (by exact PseudoEMetricSpace.toUniformSpace) = UsualTopology := by
  sorry
-- ANCHOR_END: my_usual_equiv_statement
