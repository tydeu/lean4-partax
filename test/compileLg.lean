/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax
import Partax.Test

open Partax Test
open Lean hiding Parsec
open Parser

set_option trace.Partax.compile true

/-! # Large Compile Tests
Examples of compiling large Lean categories.
-/

namespace ex

compile_parser_category conv
#match_stx conv conv |
  first
  | done
    done
  | {done}
