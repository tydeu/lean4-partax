/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test

open Partax Test Lean Parser

/-! # Parse Tests
Verify that simple parsers work properly.
-/

#match_stx numLit LParse.numLit | 32
#match_stx strLit LParse.strLit | "hello"
#match_stx ident LParse.ident | foo.bar

/- Test that we error if input remains. -/
#eval flipExcept <| LParse.numLit.run "32 45"
