/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Test.Basic
import Partax.Test.LCompile
import Lean.Elab.Frontend

/-! # Lean Compile Tests
Tests of the whole compiled Lean grammar.
-/

open Partax Test LCompile

#match_stx term term | a.1
#match_stx term term | a.{1}
#match_stx term term | true
#match_stx term term | id a
#match_stx term term | 2 + 2 = 4

#match_stx doElem doElem | return ()
#match_stx doElem doElem | if a then _
#match_stx doElem doElem | unless a do return ()

#match_stx conv conv |
  first
  | done
    done
  | {done}

#match_stx tactic tactic | exact _

#match_stx command command | opaque foo : Nat

#match_stx command command |
  theorem add_comm : ∀ (n m : Nat), n + m = m + n
  | n, 0   => Eq.symm (Nat.zero_add n)
  | n, m+1 => by
    have : succ (n + m) = succ (m + n) := by
      apply congrArg; apply Nat.add_comm
    rw [succ_add m n]
    apply this

partial def testParseFile (path : System.FilePath) : IO PUnit := do
  let opts : Lean.Options := {}
  let input ← IO.FS.readFile path
  let ictx := mkInputContext input path.toString
  let (header, parserState, messages) ← Lean.Parser.parseHeader ictx
  let (_,  lparseState) ← IO.ofExcept <| LParseM.run ictx {} do LParse.consumeIgnored
  let (lparseHeader, lparseState) ← IO.ofExcept <| Module.header.run ictx lparseState
  discard <| IO.ofExcept <| matchStxFn lparseHeader header
  let (env, messages) ← Lean.Elab.processHeader header opts messages ictx
  let env := env.setMainModule `main
  let cmdState := Lean.Elab.Command.mkState env messages opts
  loop ictx cmdState parserState lparseState
where
  loop ictx cmdState parserState lparseState := do
    if ictx.input.atEnd parserState.pos then
      return
    let scope := cmdState.scopes.head!
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, parserState, messages) := Lean.Parser.parseCommand ictx pmctx parserState cmdState.messages
    let (lparseCmd, lparseState) ← IO.ofExcept <| command.run ictx lparseState
    discard <| IO.ofExcept <| matchStxFn lparseCmd cmd
    loop ictx {cmdState with messages} parserState lparseState

#eval testParseFile <| .mk "Partax" / "Basic.lean"

partial def parseFile (path : System.FilePath) : IO PUnit := do
  let parse : LParseT IO PUnit := do
    IO.println <| toString <| ← Module.header
    let rec loop := do
      let iniPos ← getInputPos
      try
        IO.println <| toString <| ← command
        loop
      catch e =>
        if iniPos < (← getInputPos) then throw e
    loop
  let input ← IO.FS.readFile path
  let ictx := mkInputContext input path.toString
  IO.ofExcept <| ← (parse.run' ictx).run

#eval parseFile <| .mk "Partax" / "Basic.lean"
