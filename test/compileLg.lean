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

namespace ex

/-
Dry run compile of the whole Lean grammar
-/

compile_parser_category (dry) command

/-
Compile small categories first
-/

compile_parser_category prio
compile_parser_category prec
compile_parser_category level
compile_parser_category stx
compile_parser_category attr

/-
Full compile of the remaining Lean grammar
-/

namespace main

compile_parser_category command

section end -- prevent recompile when editing below

#match_stx term term | _ + 1 = 5

#match_stx doElem doElem | if _ then _

#match_stx conv conv |
  first
  | done
    done
  | {done}

#match_stx tactic tactic | exact _

#match_stx command command | axiom foo : _
