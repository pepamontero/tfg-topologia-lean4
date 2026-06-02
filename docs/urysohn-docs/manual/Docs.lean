

import VersoManual

import Docs.Examples

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
set_option verso.exampleProject "../../../UrysohnsLemma/"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "UrysohnsLemma"

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


{include 1 Docs.Examples}
