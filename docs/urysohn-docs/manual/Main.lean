/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual

import Docs
import Docs.LangToggle

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Docs

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFiles := [
    ("figuras", "figuras")
  ]
  extraHead := Docs.langToggle "es"

def main := manualMain (%doc Docs) (config := config)
