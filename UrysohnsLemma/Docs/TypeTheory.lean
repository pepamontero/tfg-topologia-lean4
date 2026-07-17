import Mathlib.Tactic

/-
Real, compiling Lean source backing the code samples in the "La teoría de tipos de
Lean" part of the "Lean Theorem Prover" chapter (`Docs/LeanProver.lean`). Each
teaching example lives in its own `section`/`namespace` so that names reused across
unrelated examples (like `f`) don't collide. Anchors are extracted verbatim by Verso,
so keep the code between `-- ANCHOR:` / `-- ANCHOR_END:` markers matching exactly what
is shown in the manual.
-/

-- ANCHOR: check_basic
#check 3    -- 3 : ℕ
#check true   -- Bool.true : Bool
-- ANCHOR_END: check_basic

-- ANCHOR: check_nat_type
#check ℕ    -- ℕ : Type
-- ANCHOR_END: check_nat_type

section VarX
-- ANCHOR: var_x
variable (X : Type)
#check X    -- X : Type
variable (x : X)
#check x    -- x : X
-- ANCHOR_END: var_x
end VarX

section VarXY
-- ANCHOR: var_xy
variable (X Y : Type)
#check X × Y    -- X × Y : Type
variable (x : X) (y : Y)
#check (x, y)    -- (x, y) : X × Y

#check X → Y    -- X → Y : Type
variable (f : X → Y)
#check f    -- f : X → Y
-- ANCHOR_END: var_xy

-- ANCHOR: apply_fx
#check f x    -- f x : Y
-- ANCHOR_END: apply_fx
end VarXY

namespace LambdaEx1
-- ANCHOR: lambda_f_def
def f := fun n ↦ n + 2
-- ANCHOR_END: lambda_f_def

-- ANCHOR: lambda_f_eval
#eval f 3    -- 5
-- ANCHOR_END: lambda_f_eval
end LambdaEx1

namespace LambdaEx2
-- ANCHOR: typed_lambda_f
def f : ℕ → ℕ := fun n => 2 * n
-- ANCHOR_END: typed_lambda_f
end LambdaEx2

-- ANCHOR: list_dependent
#check List    -- List.{u} (α : Type u) : Type u
#check List ℝ    -- List ℝ : Type
-- ANCHOR_END: list_dependent

namespace Scratch
-- ANCHOR: inductive_nat_demo
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
-- ANCHOR_END: inductive_nat_demo
end Scratch

-- ANCHOR: print_nat_rec
#print Nat.rec
    -- recursor Nat.rec.{u}  :  {motive : ℕ → Sort u} → motive Nat.zero → ((n : ℕ) → motive n → motive n.succ) → (t : ℕ) → motive t
-- ANCHOR_END: print_nat_rec

-- ANCHOR: add_def
def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)
-- ANCHOR_END: add_def

-- ANCHOR: prop_check
#check Prop    -- Prop : Type
#print True    -- inductive True : Prop
-- ANCHOR_END: prop_check

section PropVarP
-- ANCHOR: prop_var_p
variable (P : Prop)
#check P    -- P : Prop
#check ¬ P    -- ¬ P : Prop
-- ANCHOR_END: prop_var_p
end PropVarP

section PropVarPH
-- ANCHOR: prop_var_ph
variable (p : Prop)
variable (h : p)
#check h    -- h : p
-- ANCHOR_END: prop_var_ph
end PropVarPH
