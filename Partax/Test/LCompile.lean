/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Compile

/-! # Lean Grammar Test Compile
Test helper which compiles the entire Lean grammar.
-/

open scoped Lean

set_option trace.Partax.compile.result true

namespace Partax.Test.LCompile
compile_parser_category command
end Partax.Test.LCompile

open scoped Partax
compile_parser Lean.Parser.Module.header in Partax.Test.LCompile
