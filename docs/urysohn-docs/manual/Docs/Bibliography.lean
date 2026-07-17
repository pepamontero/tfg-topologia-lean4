/-
Extends Verso's built-in bibliography system (`VersoManual.Bibliography`, which
only covers `Thesis`/`InProceedings`/`ArXiv`/`Article`) with a catch-all `Misc`
entry kind for books, websites, online courses, and other sources that don't
fit those four types. Mirrors the pattern of `VersoManual.Bibliography` closely
so that `citetOther`/`citepOther`/`citehereOther` behave exactly like the
built-in `citet`/`citep`/`citehere`.
-/
import VersoManual
import VersoManual.Bibliography

open Lean Elab
open Verso Doc Elab Html
open Verso Output Html
open Verso Genre Manual
open Verso ArgParse

namespace Verso.Genre.Manual.Docs

abbrev Style := Verso.Genre.Manual.Bibliography.Style
abbrev lastName := Verso.Genre.Manual.Bibliography.Bibliography.lastName

structure Misc where
  title : Doc.Inline Manual
  authors : Array (Doc.Inline Manual)
  year : Option Int := none
  note : Doc.Inline Manual
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable, Ord

private def andList (xs : Array Html) : Html :=
  if h : xs.size = 0 then panic! "tried to construct empty list of authors"
  else if h : xs.size = 1 then xs[0]
  else if h : xs.size = 2 then xs[0] ++ " y " ++ xs[1]
  else
    open Html in
    (xs.extract 0 (xs.size - 1)).foldr (init := {{"y " {{xs.back}} }}) (· ++ ", " ++ ·)

def Misc.bibHtml [Monad m]
    (go : Doc.Inline Genre.Manual → HtmlT Manual m Html) (c : Misc) : HtmlT Manual m Html :=
  wrap <$> open Html in do
    let authors ← andList <$> c.authors.mapM go
    let yearPart := c.year.map (s!", {·}. ") |>.getD ". "
    return {{ {{authors}} {{yearPart}} {{ link {{"“" {{← go c.title}} "”"}} }} ". " {{← go c.note}} }}
where
  wrap (content : Html) : Html := {{<span class="citation">{{content}}</span>}}
  link (title : Html) : Html :=
    match c.url with
    | .none => title
    | .some u => {{<a href={{u}}>{{title}}</a>}}

def Misc.inlineHtml [Monad m]
    (go : Doc.Inline Genre.Manual → HtmlT Manual m Html)
    (ps : List Misc)
    (fmt : Style) :
    HtmlT Manual m Html := open Html in do
  match fmt with
  | .textual =>
    let out : Array Html ← ps.toArray.mapM fun p => do
      let m ← p.bibHtml go
      let yearPart := p.year.map (s!" ({·})") |>.getD ""
      pure <| {{ {{← authorHtml p}} {{yearPart}} }} ++ Marginalia.html m
    pure <| andList out
  | .parenthetical =>
    let out : Array Html ← ps.toArray.mapM fun p => do
      let m ← p.bibHtml go
      let yearPart := p.year.map (s!", {·})") |>.getD ")"
      pure <| {{" (" {{← authorHtml p}} {{yearPart}} }} ++ Marginalia.html m
    pure <| andList out
  | .here => do
    pure <| andList (← ps.toArray.mapM (·.bibHtml go))
where
  authorHtml p := open Html in do
    if p.authors.size = 0 then
      pure {{""}}
    else if h : p.authors.size = 1 then
      go p.authors[0]
    else if h : p.authors.size > 3 then
      (· ++ {{" "<em>"et al."</em>}}) <$> go p.authors[0]
    else andList <$> p.authors.mapM go

open Verso.Doc.TeX in
def Misc.bibTeX
    (go : Doc.Inline Genre.Manual → TeXT Manual (ReaderT ExtensionImpls IO) Output.TeX) (c : Misc) :
    TeXT Manual (ReaderT ExtensionImpls IO) Output.TeX := open Output.TeX in do
  let authors ← andListTeX <$> c.authors.mapM go
  let link (title : Output.TeX) : Output.TeX :=
    match c.url with
    | .none => title
    | .some u => makeLink u title
  let yearPart := c.year.map (s!", {·}. ") |>.getD ". "
  return \TeX{
    \Lean{authors} \Lean{yearPart}
    \Lean{ link \TeX{ "``" \Lean{← go c.title} "''" } } ". "
    \Lean{← go c.note}
  }
where
  andListTeX (xs : Array Output.TeX) : Output.TeX :=
    if h : xs.size = 0 then panic! "tried to construct empty list of authors"
    else if h : xs.size = 1 then xs[0]
    else if h : xs.size = 2 then xs[0] ++ " y " ++ xs[1]
    else
      open Output.TeX in
      (xs.extract 0 (xs.size - 1)).foldr (init := \TeX{"y " \Lean{xs.back} }) (· ++ ", " ++ ·)

open Verso.Doc.TeX in
def Misc.inlineTeX
    (go : Doc.Inline Genre.Manual → TeXT Manual (ReaderT ExtensionImpls IO) Output.TeX)
    (ps : List Misc)
    (fmt : Style) :
    TeXT Manual (ReaderT ExtensionImpls IO) Output.TeX := open Output.TeX in do
  match fmt with
  | .textual =>
    let out : Array Output.TeX ← ps.toArray.mapM fun p => do
      let m ← p.bibTeX go
      let yearPart := p.year.map (s!" ({·})") |>.getD ""
      pure <| \TeX{ \Lean{← authorTeX p} \Lean{yearPart} \Lean{Marginalia.TeX m} }
    pure <| andListTeX out
  | .parenthetical =>
    let out : Array Output.TeX ← ps.toArray.mapM fun p => do
      let m ← p.bibTeX go
      let yearPart := p.year.map (s!", {·})") |>.getD ")"
      pure <| \TeX{ "(" \Lean{← authorTeX p} \Lean{yearPart} " " \Lean{Marginalia.TeX m} }
    pure <| andListTeX out
  | .here => do
    pure <| andListTeX (← ps.toArray.mapM (·.bibTeX go))
where
  andListTeX (xs : Array Output.TeX) : Output.TeX :=
    if h : xs.size = 0 then panic! "tried to construct empty list of authors"
    else if h : xs.size = 1 then xs[0]
    else if h : xs.size = 2 then xs[0] ++ " y " ++ xs[1]
    else
      open Output.TeX in
      (xs.extract 0 (xs.size - 1)).foldr (init := \TeX{"y " \Lean{xs.back} }) (· ++ ", " ++ ·)
  authorTeX p := open Output.TeX in do
    if p.authors.size = 0 then
      pure .empty
    else if h : p.authors.size = 1 then
      go p.authors[0]
    else if h : p.authors.size > 3 then
      (· ++ \TeX{" " \em{"et al."} }) <$> go p.authors[0]
    else andListTeX <$> p.authors.mapM go

inline_extension Inline.citeMisc (citations : List Misc) (style : Style := .parenthetical) where
  data := ToJson.toJson (citations, style)
  traverse _ _ _ := pure none
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data _content => do
      match FromJson.fromJson? data with
      | .error e => HtmlT.logError s!"Failed to deserialize citation: {e}"; return {{""}}
      | .ok ((v, style) : List Misc × Style) =>
        Misc.inlineHtml go v style
  toTeX :=
    open Verso.Output.TeX in
    some <| fun go _ data _content => do
      match FromJson.fromJson? data with
      | .error e => TeX.logError s!"Failed to deserialize citation: {e}"; return .empty
      | .ok ((v, style) : List Misc × Style) =>
        Misc.inlineTeX go v style
  extraCss := [Marginalia.css]

structure CiteConfig where
  citations : List Name

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]

partial def CiteConfig.parse : ArgParse m CiteConfig :=
  CiteConfig.mk <$> many1 (.positional `citation .resolvedName)
where
  many1 p := (· :: ·) <$> p <*> .many p

instance : FromArgs CiteConfig m where
  fromArgs := CiteConfig.parse
end

@[role]
def citetOther : RoleExpanderOf CiteConfig
  | config, extra => do
    let xs := config.citations.map mkIdent |>.toArray
    ``(Doc.Inline.other (Inline.citeMisc ([$xs,*] : List Misc) Verso.Genre.Manual.Bibliography.Style.textual) #[$(← extra.mapM elabInline),*])

@[role]
def citepOther : RoleExpanderOf CiteConfig
  | config, extra => do
    let xs := config.citations.map mkIdent |>.toArray
    ``(Doc.Inline.other (Inline.citeMisc ([$xs,*] : List Misc) Verso.Genre.Manual.Bibliography.Style.parenthetical) #[$(← extra.mapM elabInline),*])

@[role]
def citehereOther : RoleExpanderOf CiteConfig
  | config, extra => do
    let xs := config.citations.map mkIdent |>.toArray
    ``(Doc.Inline.other (Inline.citeMisc ([$xs,*] : List Misc) Verso.Genre.Manual.Bibliography.Style.here) #[$(← extra.mapM elabInline),*])

end Verso.Genre.Manual.Docs
