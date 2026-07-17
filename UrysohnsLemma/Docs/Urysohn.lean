import Mathlib.Tactic
import UrysohnsLemma.MyDefs.my_denumerableQ

/-
Real, compiling Lean source backing the code samples in the "El Lema de Urysohn" chapter
(`Docs/Urysohn.lean`) that do not correspond to a clean, standalone declaration in the
main development (`UrysohnsLemma/Separation`, `UrysohnsLemma/MyDefs`). This covers:

1. A pedagogical example (the Fibonacci sequence) used only to illustrate how Lean
   admits inductive definitions, unrelated to the rest of the development.
2. An abbreviated preview of the non-emptiness argument used inside `exists_r`
   (`UrysohnsLemma.MyDefs.my_rs_functions`), shown in the manual with an explicit
   `sorry` standing in for the short case computation that is spelled out in full in
   the real proof.
3. Quotes of two Mathlib facts (`Real.exists_isGLB` and the definition of `IsGLB`) shown
   for exposition. They are reproduced here (under dedicated namespaces, so they do not
   clash with the real Mathlib declarations of the same name that are also in scope)
   so they still elaborate with real InfoView data; the current Mathlib source no longer
   spells `IsGLB` out literally (it is generated from `IsLUB` via the `to_dual`
   attribute), so the quote below reproduces the mathematical content directly instead
   of being pulled from Mathlib's source text.

As elsewhere in `UrysohnsLemma/Docs`, incomplete snippets are closed with a `sorry`
placed after the `-- ANCHOR_END:` marker so the file compiles without errors while the
manual only displays the text between the markers.
-/

/- §"Construcción de G": pedagogical example showing how Lean admits inductive
   definitions, illustrated with the Fibonacci sequence. Not part of the main
   development. -/
namespace DocFibExample
-- ANCHOR: Fib_def
def Fib : ℕ → ℕ := fun n ↦
  if n = 0 then 0
  else if n = 1 then 1
  else Fib (n-1) + Fib (n-2)
-- ANCHOR_END: Fib_def
end DocFibExample

/- §"Lema 4.1": abbreviated preview of the non-emptiness argument for `R` inside
   `exists_r` (`UrysohnsLemma.MyDefs.my_rs_functions`), shown with an explicit `sorry`
   in place of the short (but full) case computation used in the real proof. -/
namespace DocExistsRPreview
example (n : ℕ) (hn : n > 1) : True := by
  let R : Finset ℕ := (Finset.range n).filter (fun m ↦ f m < f n)
-- ANCHOR: exists_r_hR_nonempty_preview
  have hR : R.Nonempty
  · use 1; sorry
-- ANCHOR_END: exists_r_hR_nonempty_preview
  trivial
end DocExistsRPreview

/- §"La función F": quote of Mathlib's `Real.exists_isGLB`. -/
namespace DocRealExistsGLBQuote
-- ANCHOR: Real_exists_isGLB_quote
theorem Real.exists_isGLB {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddBelow s) :
    ∃ x, IsGLB s x
-- ANCHOR_END: Real_exists_isGLB_quote
    := _root_.Real.exists_isGLB hne hbdd
end DocRealExistsGLBQuote

/- §"La función F": quote of the definition of `IsGLB` (a greatest lower bound is the
   greatest element of the set of lower bounds). Current Mathlib no longer states this
   literally (`IsGLB` is generated from `IsLUB` via the `to_dual` attribute), so this
   reproduces the mathematical content directly. -/
namespace DocIsGLBQuote
-- ANCHOR: IsGLB_def_quote
def IsGLB [Preorder α] (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
-- ANCHOR_END: IsGLB_def_quote
end DocIsGLBQuote
