/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Test
import Partax.LParse

open Partax Test Lean Parser

/-! # Parse Tests
Verify that simple parsers work properly.
-/

-- error on input remaining
#eval flipExcept <| LParse.numLit.run "32 45"

-- `numLit`
#match_stx numLit LParse.numLit | 0
#match_stx numLit LParse.numLit | 01
#match_stx numLit LParse.numLit | 42
#match_stx numLit LParse.numLit | 0b101
#match_stx numLit LParse.numLit | 0XF6
#match_stx numLit LParse.numLit | 0o7

-- other tokens
#match_stx strLit LParse.strLit | "hello\nhello"
#match_stx scientificLit LParse.scientificLit | 2.
#match_stx ident LParse.ident | foo.bar

-- unicode symbols
def leftArrow := LParse.unicodeSymbol "← " "<- "
#match_stx Term.leftArrow leftArrow | ←
#match_stx Term.leftArrow leftArrow | <-

-- interpolated strings
def interpolatedNum := interpolatedStr numLitNoAntiquot
def Partax.LParse.interpolatedNum := interpolatedStr numLit
#match_stx interpolatedNum LParse.interpolatedNum | "a{1}b"

-- `sepBy1`
def matrix := sepBy1 (sepBy1 numLitNoAntiquot ",") "|"
def Partax.LParse.matrix := sepBy1 (sepBy1 numLit "," (atom ",")) "|" (atom "|")
#match_stx matrix LParse.matrix | 1, 2 | 3, 4 | 5, 6
