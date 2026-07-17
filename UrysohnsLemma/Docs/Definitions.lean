import Mathlib.Tactic

/-
Real, compiling Lean source backing the code samples in the "Axiomas, definiciones y
variables" and "Proposiciones" parts of the "Lean Theorem Prover" chapter
(`Docs/LeanProver.lean`). Named declarations (`axiom`/`def`) that reuse the same plain
name across unrelated examples (like `n`) are wrapped in their own `namespace` (which,
unlike a bare `section`, actually keeps the resulting global name distinct) so the file
compiles; plain `variable`s only need a `section` since those are already scoped by it.
-/

namespace AxiomP
-- ANCHOR: axiom_p_h
axiom P : Prop
axiom h : P → P
-- ANCHOR_END: axiom_p_h
end AxiomP

namespace AxiomN
-- ANCHOR: axiom_n_hn
axiom n : ℕ
axiom hn : n > 2
-- ANCHOR_END: axiom_n_hn
end AxiomN

namespace DefsBlock
-- ANCHOR: defs_f_n_espar
def f : ℕ → ℕ := fun n ↦ 2 * n
def n : ℕ := 3
def es_par : ℕ → Prop := fun n ↦ ∃ m, n = f m
-- ANCHOR_END: defs_f_n_espar
end DefsBlock

namespace DefN3
-- ANCHOR: def_n_infer
def n := 3
#check n    -- n : ℕ
-- ANCHOR_END: def_n_infer
end DefN3

section VarXAxiomHx
-- ANCHOR: var_x_axiom_hx
variable (x : ℕ)
axiom hx : x ≥ 0
#print hx    -- axiom hx : ∀ (x : ℕ), x ≥ 0
-- ANCHOR_END: var_x_axiom_hx
end VarXAxiomHx
