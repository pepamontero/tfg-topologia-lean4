/-
Entry point for the English version of the manual. Renders to `_out-en/` so
that it does not collide with the Spanish build in `_out/`.
-/

import Std.Data.HashMap
import VersoManual

import DocsEn
import Docs.LangToggle

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

def config : RenderConfig where
  destination := "_out-en"
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFiles := [
    ("figuras", "figuras")
  ]
  extraHead := Docs.langToggle "en"

def main := manualMain (%doc DocsEn) (config := config)
