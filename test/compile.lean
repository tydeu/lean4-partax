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
set_parser_compile_config {CompileConfig.lParse with
  mapName := fun r n => `TCompile ++ r ++ CompileConfig.lParse.mapName r n
}

/-
Simple example of a symbol (an atom) wrapped in a node
-/
syntax ex1 := " foo "
#print ex1
compile_parser ex1
#print TCompile.ex1
#match_stx ex1 TCompile.ex1 | foo

/-
Reference to a pre-defined (and previously compiled) piece of syntax
-/
syntax ex1i := ex1
#print ex1i
compile_parser ex1i
#match_stx ex1i TCompile.ex1i | foo

/-
Test that we properly compile syntax within a namespace
-/
namespace Foo
syntax ex1i := ex1
#print ex1i
compile_parser ex1i
#match_stx Foo.ex1i TCompile.Foo.ex1i | foo
end Foo

/-
Example of the or-else combinator with a reference to
an as of yet compiled piece of syntax
-/
syntax ex1b := "bar"
syntax exA := ex1 <|> ex1b
compile_parser exA
#match_stx exA TCompile.exA | foo
#match_stx exA TCompile.exA | bar

/-
Example of the and-then parser combinator
-/
syntax ex2 := exA "baz"+
compile_parser ex2
#match_stx ex2 TCompile.ex2 | foo baz baz

/-
Example of whitespace sensitive parsers
-/
syntax exWs := atomic(num ws ident)
syntax exNoWs := atomic(num noWs ident)
syntax exWsOrNoWs := exWs <|> exNoWs
compile_parser exWsOrNoWs
#match_stx exWsOrNoWs TCompile.exWsOrNoWs | 50ws
#match_stx exWsOrNoWs TCompile.exWsOrNoWs | 50 ws

/-
Example of compiling a real parser
-/
syntax exP := Command.docComment
compile_parser exP
#match_stx exP TCompile.exP | /-- hello/hello /- hello-hello -/ -/

/-
Example of using our own builtin aliases
-/
def LParse.decimal : LParseM Syntax :=
  LParse.atomOf do skipMany digit
def decimal : ParserDescr := .const `decimal
syntax exSepDigit := "[" decimal,* "]"
#print exSepDigit
compile_parser exSepDigit with {CompileConfig.lParse with
  mapName := fun r n => `TCompile ++ CompileConfig.lParse.mapName r n
  syntaxAliases := CompileConfig.lParse.syntaxAliases
    |>.insert `decimal ``LParse.decimal
}
#print TCompile.exSepDigit
def parseExSepDigit (str : String) :=
  TCompile.exSepDigit.run (syms := TCompile.exSepDigit.symbols) str
#eval parseExSepDigit "[]"
#eval parseExSepDigit "[0,] "
#eval parseExSepDigit " [0, 1]"

/-
Example of compiling a category
-/
declare_syntax_cat exCat
syntax "a" : exCat
syntax "b" exCat : exCat
syntax exCatP := exCat
compile_parser exCatP
#match_stx exCatP TCompile.exCatP | b b a

/-
Demonstration of compiling builtin Lean syntax
-/

set_parser_compile_config CompileConfig.lParse

namespace ex

compile_parser Tactic.caseArg
#match_stx Parser.Tactic.caseArg Tactic.caseArg | foo.bar _

compile_parser_category prio
#match_stx prio prio | default + default

open Lean Elab Command in
#eval liftMacroM (m := CommandElabM) do
  match prio.run "default" with
  | .ok stx => evalPrio stx
  | .error e => Macro.throwError e

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

compile_parser Term.attributes => attrs
#match_stx Parser.Term.attributes attrs | @[instance high, inline]

end ex

/-
Dry run compile of the whole Lean grammar
-/

namespace ex'
compile_parser_category (dry) command
end ex'
