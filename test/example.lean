/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean
import Partax

/-! # README Example Test
Test that mirrors the README
-/

open scoped Partax

compile_parser Lean.Parser.Term.attributes => attrs
#eval attrs.run' "@[instance high, inline]"

compile_parser_category prio
#eval prio.run' "default + default"

open Lean Elab Command in
#eval liftMacroM (m := CommandElabM) do
  match prio.run' "default + default" with
  | .ok stx => evalPrio stx
  | .error e => Macro.throwError e
