/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Partax.Test.Basic
import Partax.Test.LCompile

/-! # Lean Compile Tests
Tests of the whole compiled Lean grammar.
-/

open Partax Test LCompile

#match_stx term term | a.1
#match_stx term term | true
#match_stx term term | id a
#match_stx term term | 2 + 2 = 4

#match_stx doElem doElem | return ()
#match_stx doElem doElem | if a then _

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
