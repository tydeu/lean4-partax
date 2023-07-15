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

#match_stx numLit LParse.numLit | 0
#match_stx numLit LParse.numLit | 01
#match_stx numLit LParse.numLit | 42
#match_stx numLit LParse.numLit | 0b101
#match_stx numLit LParse.numLit | 0XF6
#match_stx numLit LParse.numLit | 0o7

#match_stx strLit LParse.strLit | "hello\nhello"
#match_stx ident LParse.ident | foo.bar

def leftArrow := LParse.unicodeSymbol "← " "<- "
#match_stx Term.leftArrow leftArrow | ←
#match_stx Term.leftArrow leftArrow | <-

/- Test that we error if input remains. -/
#eval flipExcept <| LParse.numLit.run "32 45"

def interpolatedNum := interpolatedStr numLitNoAntiquot
#match_stx interpolatedNum LParse.interpolatedStr LParse.numLit | "a{1}b"
