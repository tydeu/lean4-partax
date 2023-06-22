/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test

open Partax Test Lean Parser

/-! # Small Compile Tests
Examples of small fragments of syntax.
-/

set_option trace.Partax.compile true

-- Simple example of a symbol (an atom) wrapped in a node
syntax ex1 := "foo"
#print ex1
compile_parser_descr ex1
#print ex1.parsec
#match_stx ex1 ex1.parsec | foo

-- Reference to a pre-defined (and already compiled) piece of syntax
syntax ex1i := ex1
#print ex1i
compile_parser_descr ex1i
#print ex1i.parsec
#match_stx ex1i ex1i.parsec | foo

-- test that we properly compile syntax within a namespace
namespace foo
syntax ex1i := ex1
#print ex1i
compile_parser_descr ex1i
#print ex1i.parsec
#match_stx foo.ex1i ex1i.parsec | foo
end foo

/-
Example of the or-else combinator with a reference to
an as of yet compiled piece of syntax
-/
syntax ex1b := "bar"
syntax exA := ex1 <|> ex1b
compile_parser_descr exA
#print exA.parsec
#match_stx exA exA.parsec | foo
#match_stx exA exA.parsec | bar

/-
Example of the and-then parser combinator
-/
syntax ex2 := exA "baz"
compile_parser_descr ex2
#print ex2.parsec
#match_stx ex2 ex2.parsec | foo baz

-- Note that we cannot use a real parser unless we have defined an alias for it
syntax exP := Command.infix
--compile_parser_descr exP -- errors, as expected

/-
Example of using our own builtin aliases (i.e., `decimal`)
-/
def decimal : ParserDescr := .const `decimal
syntax exSepDigit := "[" decimal,* "]"
#print exSepDigit
compile_parser_descr exSepDigit
#print exSepDigit.parsec
#eval exSepDigit.parsec.run "[]"
#eval exSepDigit.parsec.run "[0,] "
#eval exSepDigit.parsec.run " [0, 1]"

/-
Demonstration of compiling builtin Lean syntax
-/
#print explicitBinders
compile_parser_descr explicitBinders
#match_stx explicitBinders explicitBinders.parsec | (foo.bar : Nat) (_ : String)

/-
Example of compiling a category
-/
declare_syntax_cat exCat
syntax "a" : exCat
syntax "b" exCat : exCat
syntax exCatP := exCat
compile_parser_descr exCatP
#match_stx exCatP exCatP.parsec | b b a

/-
Demonstration of compiling small builtin Lean categories
-/

namespace ex
compile_parser_category prio
#match_stx prio prio | default + default
