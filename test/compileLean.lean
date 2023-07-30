/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Compile
import Partax.Test.Basic

open Partax Test Lean Parser

/-! # Basic Compile Tests
Examples of Lean syntax compilations with relatively short run times.
-/

namespace ex

compile_parser Tactic.caseArg
#match_stx Parser.Tactic.caseArg Tactic.caseArg | foo.bar _

compile_parser_category prio
#match_stx prio prio | default + default

open Lean Elab Command in
#eval liftMacroM (m := CommandElabM) do
  match prio.run "default + default" with
  | .ok stx =>
    let val ← evalPrio stx
    unless val == 2000 do Macro.throwError s!"expected 2000, got {val}"
  | .error e => Macro.throwError e

compile_parser_category prec
#match_stx prec prec | max - 10

compile_parser_category level
#match_stx level level | max u
#match_stx level level | imax (u+1) _ v

compile_parser_category stx
#match_stx stx stx | ("compile_parser " ident (" as " ident)?)

compile_parser_category attr
#match_stx attr attr | custom (high + default)
#match_stx attr attr | instance (high + default)

compile_parser Term.attributes => attrs
#match_stx Parser.Term.attributes attrs | @[instance high, inline]

end ex

/-
Dry run compile of the whole Lean grammar
-/

namespace ex'
compile_parser_category (dry) command
end ex'
