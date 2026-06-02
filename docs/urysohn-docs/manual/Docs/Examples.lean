
import VersoManual

-- This gets access to most of the manual genre (which is also useful for textbooks)
open Verso.Genre Manual


-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean
open Verso.Code.External


set_option pp.rawOnError true

set_option verso.exampleProject "../../.."
set_option verso.exampleModule "UrysohnsLemma.TopoSpaces.discrete"


#doc (Manual) "Examples" =>
%%%
htmlSplit := .never
%%%

# Topological spaces

:::paragraph
*Ejemplo:* La _topología discreta_ sobre un conjunto $`X` es el espacio...
:::

```anchor DiscreteTopo
```
