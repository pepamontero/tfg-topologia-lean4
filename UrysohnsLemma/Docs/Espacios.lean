import Mathlib.Tactic

/-
Real, compiling Lean source backing the code samples in the "Espacios topológicos en
Lean" chapter (`Docs/Espacios.lean`) that do not correspond to a clean, standalone
declaration in the main development (`UrysohnsLemma/TopoSpaces`, `BasicProp`,
`Continuous`, `Separation`). This covers two situations:

1. Snippets that are literal quotes of Mathlib's own definitions (`TopologicalSpace`,
   `IsClosed`, `interior`, `closure`, `Continuous`), shown for exposition rather than as
   part of the project's own code. Reproducing them here (under a dedicated namespace,
   so they do not clash with the real Mathlib declarations of the same name that are
   also in scope via `import Mathlib.Tactic`) lets them still elaborate with real
   InfoView data.
2. A few small standalone `example`s that illustrate a single fact directly from a
   definition and were never factored out as their own named declaration in the main
   development.

As elsewhere in `UrysohnsLemma/Docs`, incomplete snippets are closed with a `sorry`
placed after the `-- ANCHOR_END:` marker so the file compiles without errors while the
manual only displays the text between the markers.
-/

/- §"Espacios topológicos", Definición 3.1: quote of Mathlib's `TopologicalSpace` class. -/
namespace DocTopologicalSpaceQuote
-- ANCHOR: topologicalSpace_class_quote
class TopologicalSpace (X : Type u) where
  IsOpen : Set X → Prop
  isOpen_univ : IsOpen Set.univ
  isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
-- ANCHOR_END: topologicalSpace_class_quote
end DocTopologicalSpaceQuote

/- §"Conjuntos abiertos", Ejemplo 3.4: not factored out as its own declaration anywhere
in `BasicProp`, so it is reproduced here verbatim (uses the real Mathlib
`TopologicalSpace`). -/
-- ANCHOR: univ_isOpen_example
example (X : Type) [T : TopologicalSpace X] : T.IsOpen Set.univ := by
  exact TopologicalSpace.isOpen_univ
-- ANCHOR_END: univ_isOpen_example

/- §"Conjuntos abiertos", Definición 3.4: quote of Mathlib's `interior` definition. -/
namespace DocInteriorQuote
variable {X : Type u} [TopologicalSpace X]
-- ANCHOR: interior_def_quote
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }
-- ANCHOR_END: interior_def_quote
end DocInteriorQuote

/- §"Conjuntos cerrados", Definición 3.5: quote of Mathlib's `IsClosed` class. -/
namespace DocIsClosedQuote
variable {X : Type u} [TopologicalSpace X]
-- ANCHOR: isClosed_class_quote
class IsClosed (s : Set X) : Prop where
  isOpen_compl : IsOpen sᶜ
-- ANCHOR_END: isClosed_class_quote
end DocIsClosedQuote

/- §"Conjuntos cerrados", Definición 3.6: quote of Mathlib's `closure` definition. -/
namespace DocClosureQuote
variable {X : Type u} [TopologicalSpace X]
-- ANCHOR: closure_def_quote
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }
-- ANCHOR_END: closure_def_quote
end DocClosureQuote

/- §"Continuidad", Definición 3.9: quote of Mathlib's characterization of `Continuous`
as a structure (Mathlib itself states it as a `class`, but the manual presents it as a
`structure`; both are valid, equivalent ways to state the same predicate). -/
namespace DocContinuousQuote
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
-- ANCHOR: continuous_structure_quote
structure Continuous (f : X → Y) : Prop where
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)
-- ANCHOR_END: continuous_structure_quote
end DocContinuousQuote

/- §"Separación", Definición 3.10: illustrative, unfolded characterization of a normal
space (`∀` closed pairs, `∃` disjoint open separators via `∩ = ∅`). Mathlib's actual
`NormalSpace` class has a different shape (via `SeparatedNhds`/`Disjoint`); the manual's
margin note explains that the project instead works with this equivalent formulation,
proved equivalent to Mathlib's class by `normal_space_def`
(`UrysohnsLemma/Separation/normal.lean`). This definition is shown once for exposition
and is not used elsewhere in the code, so it is kept standalone here. -/
namespace DocNormalSpaceQuote
-- ANCHOR: NormalSpace_illustrative_def
def NormalSpace {X : Type} (T : TopologicalSpace X) : Prop :=
  ∀ C : Set X, ∀ D : Set X,
  IsClosed C → IsClosed D → C ∩ D = ∅ →
  ∃ U : Set X, ∃ V : Set X,
    IsOpen U ∧ IsOpen V ∧ C ⊆ U ∧ D ⊆ V ∧ U ∩ V = ∅
-- ANCHOR_END: NormalSpace_illustrative_def
end DocNormalSpaceQuote
