/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test

open Partax Test Lean Parser

set_option trace.Partax.compile.result true

/-! # Large Compile Tests
Examples of compiling large Lean categories.
-/

compile_parser_category (dry) command
