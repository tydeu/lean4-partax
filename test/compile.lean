/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Compile
import Partax.Test.Basic

open Partax Test Lean Parser

/-! # Basic Compile Tests
Examples of syntax compilations with relatively short run times.
-/

set_option trace.Partax.compile true

/-
Simple example of a symbol (an atom) wrapped in a node
-/
syntax ex1 := " foo "
#print ex1
compile_parser ex1
#print ex1.lParse.ex1
#match_stx ex1 ex1.lParse | foo

/-
Reference to a pre-defined (and previously compiled) piece of syntax
-/
syntax ex1i := ex1
#print ex1i
compile_parser ex1i
#match_stx ex1i ex1i.lParse | foo

/-
Test that we properly compile syntax within a namespace
-/
namespace Foo
syntax ex1i := ex1
#print ex1i
compile_parser ex1i
#match_stx Foo.ex1i ex1i.lParse | foo
end Foo

/-
Example of the or-else combinator with a reference to
an as of yet compiled piece of syntax
-/
syntax ex1b := "bar"
syntax exA := ex1 <|> ex1b
compile_parser exA
#match_stx exA exA.lParse | foo
#match_stx exA exA.lParse | bar

/-
Example of the and-then parser combinator
-/
syntax ex2 := exA "baz"+
compile_parser ex2
#match_stx ex2 ex2.lParse | foo baz baz

/-
Example of whitespace sensitive parsers
-/
syntax exWs := atomic(num ws ident)
syntax exNoWs := atomic(num noWs ident)
syntax exWsOrNoWs := exWs <|> exNoWs
compile_parser exWsOrNoWs
#match_stx exWsOrNoWs exWsOrNoWs.lParse | 50ws
#match_stx exWsOrNoWs exWsOrNoWs.lParse | 50 ws

/-
Example of compiling a real parser
-/
syntax exP := Command.docComment
compile_parser exP
#match_stx exP exP.lParse | /-- hello/hello /- hello-hello -/ -/

/-
Example of using our own builtin aliases
-/
def LParse.decimal : LParse Syntax :=
  LParse.atomOf do skipMany digit
def decimal : ParserDescr := .const `decimal
syntax exSepDigit := "[" decimal,* "]"
#print exSepDigit
compile_parser exSepDigit with {CompileConfig.lparse with
  syntaxAliases := CompileConfig.lparse.syntaxAliases
    |>.insert `decimal ``LParse.decimal
}
#print exSepDigit.lParse.exSepDigit
def parseExSepDigit (str : String) :=
  exSepDigit.lParse.run (syms := exSepDigit.lParse.symbols) str
#eval parseExSepDigit "[]"
#eval parseExSepDigit "[0,] "
#eval parseExSepDigit " [0, 1]"

/-
Demonstration of compiling builtin Lean syntax
-/
#print Tactic.caseArg
compile_parser Tactic.caseArg
#match_stx Tactic.caseArg Tactic.caseArg.lParse | foo.bar _

/-
Example of compiling a category
-/
declare_syntax_cat exCat
syntax "a" : exCat
syntax "b" exCat : exCat
syntax exCatP := exCat
compile_parser exCatP
#match_stx exCatP exCatP.lParse | b b a

/-
Demonstration of compiling small builtin Lean categories
-/
namespace ex

compile_parser_category prio
#match_stx prio prio | default + default

compile_parser_category prec
#match_stx prec prec | max - 10

compile_parser_category level
#match_stx level level | max u
#match_stx level level | imax (u+1) _ v

compile_parser_category stx
#match_stx stx stx | ("compile_parser " ident (" as " ident)?)

compile_parser_category attr
#match_stx attr attr | custom (high + default)
#match_stx attr attr | instance (high + default)

end ex

/-
Dry run compile of the whole Lean grammar
-/
namespace ex'
compile_parser_category (dry) command
end ex'
