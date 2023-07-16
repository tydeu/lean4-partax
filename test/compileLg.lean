/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test
import Partax.TestCompile

open Partax Lean Test Parser

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
Test of the compiled Lean grammar
-/

open LParse

#match_stx term term | true

#match_stx term term | _ + 1 = 5

#match_stx doElem doElem | if a then _

#match_stx conv conv |
  first
  | done
    done
  | {done}

#match_stx tactic tactic | exact _

#match_stx command command | opaque foo : Nat
