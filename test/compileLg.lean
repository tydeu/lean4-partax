/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test

open Partax Test Lean Parser

set_option trace.Partax.compile.result true

/-! # Large Compile Tests
Test of compiling large Lean categories.
-/

/-
Compile small categories first to decrease mutual size
-/

compile_parser_category prio
compile_parser_category prec
compile_parser_category level
compile_parser_category stx
compile_parser_category attr

/-
Dry run compile of the whole Lean Grammar
-/

compile_parser_category (dry) command
