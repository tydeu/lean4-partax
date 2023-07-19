/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax.Test
import Partax.TestCompile

/-! # Large Compile Tests
Test of compiling large Lean categories.
-/

open Partax Test

/-
Test of the compiled Lean grammar
-/

open LCompile

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
