import VersoManual

import Docs.Introduccion
import Docs.LeanProver
import Docs.Espacios
import Docs.Urysohn
import Docs.Conclusion
import Docs.Referencias

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Formalización de las matemáticas con Lean. Un caso de estudio: Resultados de Topología General." =>
%%%
authors := ["Pepa Montero Jimena"]
shortTitle := "Formalización de las matemáticas con Lean"
date := "Julio de 2025"
authorshipNote := "Dirigido por Jorge Carmona Ruber"
%%%

Trabajo de Fin de Grado — Curso 2024/2025.

Facultad de Ciencias Matemáticas, Grado en Matemáticas, Departamento de Sistemas Informáticos y Computación, Universidad Complutense de Madrid.

# Resumen
%%%
number := false
%%%

Este trabajo consiste en una exploración del sistema Lean 4 como asistente de demostración, mediante un caso de estudio: la formalización de resultados de topología general. El objetivo principal es profundizar en el aprendizaje de este sistema y obtener una visión crítica de las ventajas y los inconvenientes que presenta al escribir matemáticas. Se presenta un acercamiento general a la base fundacional del sistema, su sintaxis y su aplicación concreta a la topología. Finalmente, se detalla el proceso de formalización de un resultado complejo como es el Lema de Urysohn, junto con las conclusiones obtenidas del trabajo realizado.

# Abstract
%%%
number := false
%%%

This project consists of an exploration of the Lean 4 system as a proof assistant through a case study: the formalisation of results in general topology. The main objective is to deepen the understanding of this system and to provide a critical perspective on its advantages and disadvantages when writing mathematics. A general overview of the foundational basis of the system, its syntax, and its concrete application to topology is provided. The project concludes with a description of the process of formalising the more complex result Urysohn's Lemma, as well as the insights gained throughout the work.

{include 1 Docs.Introduccion}

{include 1 Docs.LeanProver}

{include 1 Docs.Espacios}

{include 1 Docs.Urysohn}

{include 1 Docs.Conclusion}

{include 1 Docs.Referencias}
