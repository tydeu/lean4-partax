/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Compile
import Partax.Test.Basic

open Partax Test Lean Parser

/-! # Basic Compile Tests
Examples of Custom syntax compilations with relatively short run times.
-/

set_option trace.Partax.compile true

/-
A compile config that embeds nested compiled nodes into the root node's namespace
Allows tests to compile the same node twice without changing namespaces.
-/
def compileConfig := {CompileConfig.lParse with
  mapName := fun r n =>
    let base := CompileConfig.lParse.mapName r n
    if r.isAnonymous then `TCompile ++ base else r ++ `kinds ++ base
}

set_parser_compile_config compileConfig

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
Example of compiling a category
-/
declare_syntax_cat exCat
syntax "a" : exCat
syntax "b" exCat : exCat
syntax exCatP := exCat
compile_parser exCatP
#match_stx exCatP TCompile.exCatP | b b a


/-
Example of using our own builtin aliases
-/
def LParse.decimal : LParseM Syntax :=
  LParse.atomOf do skipMany digit
def decimal : ParserDescr := .const `decimal
syntax exSepDigit := "[" decimal,* "]"
#print exSepDigit
compile_parser exSepDigit with {compileConfig with
  syntaxAliases := compileConfig.syntaxAliases
    |>.insert `decimal ``LParse.decimal
}
#print TCompile.exSepDigit
#eval TCompile.exSepDigit.run "[]"
#eval TCompile.exSepDigit.run "[0,] "
#eval TCompile.exSepDigit.run " [0, 1]"
