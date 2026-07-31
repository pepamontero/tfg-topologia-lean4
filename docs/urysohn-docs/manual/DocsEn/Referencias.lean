import VersoManual
import Docs.Papers

open Verso.Genre Manual

set_option pp.rawOnError true
-- Keep this in every translated chapter so bibliography text renders in English:
set_option docs.bib.lang "en"

#doc (Manual) "References" =>
%%%
tag := "referencias"
number := false
file := "referencias"
htmlSplit := .never
%%%

🚧 _The full list of references is available in the [Spanish version](../referencias/) of this document._
