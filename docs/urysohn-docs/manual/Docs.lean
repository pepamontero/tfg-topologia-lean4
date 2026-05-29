

import VersoManual

import Docs.Papers
import Docs.DocFeatures

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules.
open Verso.Code.External

open Docs

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../zippers"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "Zippers"

#doc (Manual) "Formalización de las matemáticas con
Lean. Resultados de
Topología General y Lema de Urysohn." =>
%%%
authors := ["Pepa Montero"]
shortTitle := "UrysohnsLemma"
%%%

Este trabajo consiste en una exploración del sistema Lean 4 como asistente de demostración, mediante un caso de estudio: la formalización de resultados de topología general.

El objetivo principal es profundizar en el aprendizaje de este sistema y obtener una visión crítica de las ventajas y los inconvenientes que presenta al escribir matemáticas. Se presenta un acercamiento general a la base fundacional del sistema, su sintaxis y su aplicación concreta a la topología.

Finalmente, se detalla el proceso de formalización de un resultado complejo como es el Lema de Urysohn, junto con las conclusiones obtenidas del trabajo realizado.

# Zippers

A _zipper_{citep theZipper}[] is a purely-functional cursor into a data structure.
They're equivalent to maintaining a description of a position (e.g. an index into a list or a series of left-right subtree decisions in a tree), but do not require traversing the prefix of the data structure.
Zippers are efficient when many modifications to a persistent structure are concentrated near each other.

:::paragraph
In this example zipper library, a zipper for some type {anchorTerm Zipper}`α` is indicated with an instance of {anchorTerm Zipper}`Zipper`:

```anchor Zipper
class Zipper
    (α : outParam (Type u)) (δ : outParam (Type w))
    (ζ : Type v) where
  move : ζ → δ → Option ζ
  close : ζ → α
  init : α → ζ
```

The type {anchorTerm Zipper}`δ` indicates the directions in which a zipper may move.
:::

:::paragraph
A lawful zipper is one in which initializing and closing zippers are inverse.
A lawful zipper for some type {anchorTerm LawfulZipper}`α` is indicated with an instance of {anchorTerm LawfulZipper}`LawfulZipper`:

```anchor LawfulZipper
class LawfulZipper
    (α : Type u) (δ : outParam (Type w)) (ζ : outParam (Type v))
    extends Zipper α δ ζ where
  init_close {x : α} : close (init x) = x
  close_init {x : ζ} : close (init (close x)) = close x
```
:::

:::paragraph
There's some syntax for moving a zipper.
The `⇰` operator attempts to move in a direction.
Here's a list zipper in action:
```anchor ex1
def z1 : ListZipper Nat := Zipper.init [1, 2, 4]
#eval z1 ⇰ .right
```
```anchorInfo ex1
some { revBefore := [1], after := [2, 4] }
```

```anchor ex2
#eval show Option (List Nat) from do
  let z ← z1 ⇰ .right
  let z ← z ⇰ .right
  let z := z.add 3
  pure z.close
```
```anchorInfo ex2
some [1, 2, 3, 4]
```
:::

:::paragraph
List zippers are defined as follows:
```anchor ListZipper
structure ListZipper (α) where
  revBefore : List α
  after : List α
deriving Repr
```
They contain the reversed prefix to the current point and the suffix after it.
To convert them back to a list, use {anchorName ListZipper.close (show:=close)}`ListZipper.close`:
```anchor ListZipper.close
def ListZipper.close (z : ListZipper α) : List α :=
  close' z.revBefore z.after
where
  close'
    | [], acc => acc
    | x :: xs, acc => close' xs (x :: acc)
```
To add an element at the current position, use {anchorName ListZipper.add (show:=add)}`ListZipper.add`:
```anchor ListZipper.add
def ListZipper.add (x : α) (xs : ListZipper α) : ListZipper α :=
  { xs with after := x :: xs.after }
```
:::

:::paragraph
Here's the instance:
```anchor Dir
inductive Dir where
  | left | right
```
```anchor ListZipperInst
instance : Zipper (List α) Dir (ListZipper α) where
  move
    | ⟨[], _⟩, .left => none
    | ⟨x :: pre, post⟩, .left => some ⟨pre, x :: post⟩
    | ⟨_, []⟩, .right => none
    | ⟨pre, x :: post⟩, .right => some ⟨x :: pre, post⟩
  close z := z.close
  init xs := ⟨[], xs⟩
```

:::
