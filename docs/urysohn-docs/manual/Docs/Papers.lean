import VersoManual
import Docs.Bibliography

open Verso.Genre.Manual
open Verso.Genre.Manual.Docs

namespace Docs

def refTrinh2024Solving : Article where
  title := inlines!"Solving olympiad geometry without human demonstrations"
  authors := #[inlines!"Trieu H. Trinh", inlines!"Yuhuai Wu", inlines!"Quoc V. Le", inlines!"He He", inlines!"Thang Luong"]
  journal := inlines!"Nature"
  year := 2024
  month := none
  volume := inlines!"625"
  number := inlines!"7995"
  pages := some (476, 482)

def refGeuvers2009Proof : Article where
  title := inlines!"Proof assistants: History, ideas and future"
  authors := #[inlines!"Herman Geuvers"]
  journal := inlines!"Sadhana"
  year := 2009
  month := none
  volume := inlines!"34"
  number := inlines!""
  pages := some (3, 25)

def refCoquand1986Calculus : Thesis where
  title := inlines!"The calculus of constructions"
  author := inlines!"Thierry Coquand y Gérard Huet"
  year := 1986
  university := inlines!"INRIA"
  degree := inlines!"Tesis doctoral"

def refGao2024Semantic : ArXiv where
  title := inlines!"A semantic search engine for Mathlib4"
  authors := #[inlines!"Guoxiong Gao", inlines!"Haocheng Ju", inlines!"Jiedong Jiang", inlines!"Zihan Qin", inlines!"Bin Dong"]
  year := 2024
  id := "2403.13310"

def refBuzzard2024Formalising : Misc where
  title := inlines!"Formalising Mathematics 2024"
  authors := #[inlines!"Kevin Buzzard"]
  year := some 2024
  note := inlines!"Imperial College London. Última consulta: 22 de junio de 2025."
  url := some "https://github.com/ImperialCollegeLondon/formalising-mathematics-2024"

def refAvigad2024Theorem : Misc where
  title := inlines!"Theorem Proving in Lean 4"
  authors := #[inlines!"Jeremy Avigad", inlines!"Leonardo De Moura", inlines!"Soonho Kong", inlines!"Sebastian Ullrich", inlines!"contribuidores de la comunidad Lean"]
  year := some 2024
  note := inlines!"Última consulta: 23 de abril de 2025."
  url := some "https://leanprover.github.io/theorem_proving_in_lean4"

def refMathlib : Misc where
  title := inlines!"mathlib4: The Lean4 Mathematical Library"
  authors := #[inlines!"Lean Prover Community"]
  year := none
  note := inlines!"Última consulta: 23 de abril de 2025."
  url := some "https://github.com/leanprover-community/mathlib4"

def refBailey2024Type : Misc where
  title := inlines!"Type Checking in Lean 4"
  authors := #[inlines!"Christopher A. Bailey", inlines!"contribuidores de la comunidad Lean"]
  year := some 2024
  note := inlines!"Última consulta: 23 de abril de 2025."
  url := some "https://ammkrn.github.io/type_checking_in_lean4"

def refAvigad2021Theorem : Misc where
  title := inlines!"Theorem proving in Lean"
  authors := #[inlines!"Jeremy Avigad", inlines!"Leonardo De Moura", inlines!"Soonho Kong"]
  year := some 2021
  note := inlines!""

def refSorensen2006Lectures : Misc where
  title := inlines!"Lectures on the Curry-Howard isomorphism"
  authors := #[inlines!"Morten Heine Sørensen", inlines!"Pawel Urzyczyn"]
  year := some 2006
  note := inlines!"Volumen 149. Elsevier. Capítulo 5, \"The Untyped Lambda Calculus\"."

def refPierce2002Types : Misc where
  title := inlines!"Types and programming languages"
  authors := #[inlines!"Benjamin C. Pierce"]
  year := some 2002
  note := inlines!"MIT press."

def refCarneiro2019Type : Misc where
  title := inlines!"The Type Theory of Lean"
  authors := #[inlines!"Mario Carneiro"]
  year := some 2019
  note := inlines!"Sección 5, \"Reduction of inductive types to W-types\"."

def refCarneiro2024Lean4Lean : Misc where
  title := inlines!"Lean4Lean: Towards a formalized metatheory for the Lean theorem prover"
  authors := #[inlines!"Mario Carneiro"]
  year := some 2024
  note := inlines!"arXiv e-prints, arXiv:2403."

def refTacticas : Misc where
  title := inlines!"Mathlib manual: Tactics"
  authors := #[inlines!"Lean Prover Community"]
  year := some 2023
  note := inlines!"Última consulta: 24 de junio de 2025."
  url := some "https://leanprover-community.github.io/mathlib-manual/html-multi/Tactics/#tactics"

def refMoogle : Misc where
  title := inlines!"Moogle, a semantic search engine for Mathlib, the Lean mathematical library"
  authors := #[inlines!"Morph"]
  year := some 2023
  note := inlines!"Última consulta: 24 de mayo de 2025."
  url := some "https://www.moogle.ai/"

def refWillard2012General : Misc where
  title := inlines!"General topology"
  authors := #[inlines!"Stephen Willard"]
  year := some 2012
  note := inlines!"Courier Corporation."

def refMathlib2023Urysohn : Misc where
  title := inlines!"Urysohn's lemma"
  authors := #[inlines!"Lean Prover Community"]
  year := some 2023
  note := inlines!"Última consulta: 22 de junio de 2025."
  url := some "https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/UrysohnsLemma.html"

end Docs
