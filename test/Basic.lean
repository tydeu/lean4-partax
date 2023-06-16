/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax
import Lean.Parser.Basic

open Lean Parser

-- Simple example of a symbol (an atom) wrapped in a node
syntax ex1 := "foo"
#print ex1
compile_parser_descr ex1
#print ex1.parsec
--#print ex1.parsec.raw
#eval ex1.parsec.run " foo "

-- Reference to a pre-defined (and already compiled) piece of syntax
syntax ex1i := ex1
#print ex1i
compile_parser_descr ex1i
#print ex1i.parsec
#eval ex1i.parsec.run " foo "

-- test that we properly compile syntax within a namespace
namespace foo
syntax ex1i := ex1
#print ex1i
compile_parser_descr ex1i
#print ex1i.parsec
#eval ex1i.parsec.run " foo "
end foo

/-
Example of the or-else combinator with a reference to
an as of yet compiled piece of syntax
-/
syntax ex1b := "bar"
syntax exA := ex1 <|> ex1b
compile_parser_descr exA
--#print exA.parsec.raw
--#print ex1b.parsec
#print exA.parsec
#eval exA.parsec.run " foo "
#eval exA.parsec.run " bar "

-- Example of the and-then parser combinator
syntax ex2 := exA "baz"
compile_parser_descr ex2
--#print ex2.parsec.raw
#print ex2.parsec
#eval ex2.parsec.run " foo   baz "

-- Note that we cannot use a real parser unless we have defined an alias for it
syntax exP := Command.infix
--compile_parser_descr exP -- errors, as expected

-- Example of using our own builtin aliases (i.e., `decimal`)
def decimal : ParserDescr := .const `decimal
syntax exSepDigit := "[" decimal,* "]"
#print exSepDigit
compile_parser_descr exSepDigit
--#print exSepDigit.parsec.raw
#print exSepDigit.parsec
#eval exSepDigit.parsec.run "[]"
--#eval exSepDigit.parsec.run "[0,] "
#eval exSepDigit.parsec.run " [0, 1]"

-- Demonstration of compiling builtin Lean syntax
compile_parser_descr explicitBinders
--#check binderIdent.parsec.raw
--#eval binderIdent.parsec.run "foo.bar"
#eval explicitBinders.parsec.run "(foo.bar : Nat) (_ : String)"

-- Example of compiling a category
declare_syntax_cat exCat
syntax "a" : exCat
syntax "b" exCat : exCat
syntax exCatP := exCat
compile_parser_descr exCatP
#eval exCatP.parsec.run "b b a"

-- Demonstration of compiling a whole builtin Lean category
syntax exBuiltinCat := prio
compile_parser_descr exBuiltinCat
compile_parser_category prio in ex
