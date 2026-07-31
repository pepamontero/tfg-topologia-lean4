import VersoManual

import DocsEn.Introduccion
import DocsEn.LeanProver
import DocsEn.Espacios
import DocsEn.Urysohn
import DocsEn.Conclusion
import DocsEn.Referencias

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Formalising Mathematics with Lean. A Case Study: Results in General Topology." =>
%%%
authors := ["Pepa Montero Jimena"]
shortTitle := "Formalising Mathematics with Lean"
date := "July 2025"
authorshipNote := "Supervised by Jorge Carmona Ruber"
%%%

Bachelor's Thesis (Trabajo de Fin de Grado) — Academic year 2024/2025.

Faculty of Mathematical Sciences, Degree in Mathematics, Department of Computer Systems and Computing, Universidad Complutense de Madrid.

# Abstract
%%%
number := false
file := "abstract"
%%%

This project consists of an exploration of the Lean 4 system as a proof assistant through a case study: the formalisation of results in general topology. The main objective is to deepen the understanding of this system and to provide a critical perspective on its advantages and disadvantages when writing mathematics. A general overview of the foundational basis of the system, its syntax, and its concrete application to topology is provided. The project concludes with a description of the process of formalising the more complex result Urysohn's Lemma, as well as the insights gained throughout the work.

{include 1 DocsEn.Introduccion}

{include 1 DocsEn.LeanProver}

{include 1 DocsEn.Espacios}

{include 1 DocsEn.Urysohn}

{include 1 DocsEn.Conclusion}

{include 1 DocsEn.Referencias}
