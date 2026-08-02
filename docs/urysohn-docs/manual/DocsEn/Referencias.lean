import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.Docs (citehereOther)
open Docs (refTrinh2024Solving refGeuvers2009Proof refBuzzard2024Formalising
  refAvigad2024Theorem refMathlib refBailey2024Type refAvigad2021Theorem
  refSorensen2006Lectures refCoquand1986Calculus refPierce2002Types refCarneiro2019Type
  refCarneiro2024Lean4Lean refTacticas refMoogle refGao2024Semantic
  refWillard2012General refMathlib2023Urysohn)

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"

#doc (Manual) "References" =>
%%%
tag := "referencias"
number := false
file := "referencias"
%%%

# \[1\] Trinh, Wu, Le, He and Luong (2024)
%%%
tag := "ref-trinh2024solving"
file := "ref-trinh2024solving"
number := false
%%%

{citehere refTrinh2024Solving}[]

# \[2\] Geuvers (2009)
%%%
tag := "ref-geuvers2009proof"
file := "ref-geuvers2009proof"
number := false
%%%

{citehere refGeuvers2009Proof}[]

# \[3\] Buzzard (2024)
%%%
tag := "ref-buzzard2024formalising"
file := "ref-buzzard2024formalising"
number := false
%%%

{citehereOther refBuzzard2024Formalising}[]

# \[4\] Avigad, De Moura, Kong, Ullrich and Lean community contributors (2024)
%%%
tag := "ref-avigad2024theorem"
file := "ref-avigad2024theorem"
number := false
%%%

{citehereOther refAvigad2024Theorem}[]

# \[5\] Lean Prover Community
%%%
tag := "ref-mathlib"
file := "ref-mathlib"
number := false
%%%

{citehereOther refMathlib}[]

# \[6\] Bailey and Lean community contributors (2024)
%%%
tag := "ref-bailey2024type"
file := "ref-bailey2024type"
number := false
%%%

{citehereOther refBailey2024Type}[]

# \[7\] Avigad, De Moura and Kong (2021)
%%%
tag := "ref-avigad2021theorem"
file := "ref-avigad2021theorem"
number := false
%%%

{citehereOther refAvigad2021Theorem}[]

# \[8\] Sørensen and Urzyczyn (2006)
%%%
tag := "ref-sorensen2006lectures"
file := "ref-sorensen2006lectures"
number := false
%%%

{citehereOther refSorensen2006Lectures}[]

# \[9\] Coquand and Huet (1986)
%%%
tag := "ref-coquand1986calculus"
file := "ref-coquand1986calculus"
number := false
%%%

{citehere refCoquand1986Calculus}[]

# \[10\] Pierce (2002)
%%%
tag := "ref-pierce2002types"
file := "ref-pierce2002types"
number := false
%%%

{citehereOther refPierce2002Types}[]

# \[11\] Carneiro (2019)
%%%
tag := "ref-carneiro2019type"
file := "ref-carneiro2019type"
number := false
%%%

{citehereOther refCarneiro2019Type}[]

# \[12\] Carneiro (2024)
%%%
tag := "ref-carneiro2024lean4lean"
file := "ref-carneiro2024lean4lean"
number := false
%%%

{citehereOther refCarneiro2024Lean4Lean}[]

# \[13\] Lean Prover Community (2023)
%%%
tag := "ref-tacticas"
file := "ref-tacticas"
number := false
%%%

{citehereOther refTacticas}[]

# \[14\] Morph (2023)
%%%
tag := "ref-moogle"
file := "ref-moogle"
number := false
%%%

{citehereOther refMoogle}[]

# \[15\] Gao, Ju, Jiang, Qin and Dong (2024)
%%%
tag := "ref-gao2024semantic"
file := "ref-gao2024semantic"
number := false
%%%

{citehere refGao2024Semantic}[]

# \[16\] Willard (2012)
%%%
tag := "ref-willard2012general"
file := "ref-willard2012general"
number := false
%%%

{citehereOther refWillard2012General}[]

# \[17\] Lean Prover Community (2023)
%%%
tag := "ref-mathlib2023urysohn"
file := "ref-mathlib2023urysohn"
number := false
%%%

{citehereOther refMathlib2023Urysohn}[]
