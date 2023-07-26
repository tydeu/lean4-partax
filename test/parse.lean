/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.LParse
import Partax.Test.Basic

open Partax Test Lean Parser

/-! # Parse Tests
Verify that simple parsers work properly.
-/

-- error on input remaining
#eval flipExcept <| LParse.numLit.run "32 45"

-- ident
#match_stx ident LParse.ident | «foo»
#match_stx ident LParse.ident | foo.bar

-- ident end
def identField := node `null <| ident >> "." >> fieldIdx
def Partax.LParse.identField := node `null <| ident >> atom "." >> fieldIdx
#match_stx identField LParse.identField | foo.1

-- `numLit`
#match_stx numLit LParse.numLit | 0
#match_stx numLit LParse.numLit | 01
#match_stx numLit LParse.numLit | 42
#match_stx numLit LParse.numLit | 0b101
#match_stx numLit LParse.numLit | 0XF6
#match_stx numLit LParse.numLit | 0o7

-- `charLit`
#match_stx charLit LParse.charLit | 'a'
#match_stx charLit LParse.charLit | '\\'
#match_stx charLit LParse.charLit | '\x00'

-- other tokens
#match_stx strLit LParse.strLit | "hello\nhello"
#match_stx scientificLit LParse.scientificLit | 2.

-- unicode symbols
def leftArrow := LParse.unicodeSymbol "← " "<- "
#match_stx Term.leftArrow leftArrow | ←
#match_stx Term.leftArrow leftArrow | <-

-- interpolated strings
def interpolatedNum := node `null <| interpolatedStr numLit >> numLit
def Partax.LParse.interpolatedNum := node `null <| interpolatedStr numLit >> numLit
#match_stx interpolatedNum LParse.interpolatedNum | "a{1}b" 1

-- `sepBy1`
def matrix := sepBy1 (sepBy1 numLit ",") "|"
def Partax.LParse.matrix := sepBy1 (sepBy1 numLit "," (atom ",")) "|" (atom "|")
#match_stx matrix LParse.matrix | 1, 2 | 3, 4 | 5, 6
