/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Data.Parsec

namespace Partax
export Lean (Parsec)
namespace Parsec
open Lean.Parsec

--------------------------------------------------------------------------------
-- # General Parsec Helpers
--------------------------------------------------------------------------------

instance : MonadReaderOf String.Iterator Parsec where
  read := fun it => .success it it

@[inline] def option (p : Parsec α) : Parsec (Option α) := fun it =>
  match p it with
  | .success it a => .success it (some a)
  | .error _ _ => .success it none

@[inline] def matched (p : Parsec α) : Parsec Bool := fun it =>
  match p it with
  | .success it _ => .success it true
  | .error _ _  => .success it false

@[inline] def withString (p : Parsec α) : Parsec (String × α) := fun it =>
  match p it with
  | .success it' a => .success it' (it.extract it', a)
  | .error it' e  => .error it' e

@[inline] def extract (p : Parsec α) : Parsec String :=
  (·.1) <$> withString p

@[inline] def withSubstring (p : Parsec α) : Parsec (Substring × α) := fun it =>
  match p it with
  | .success it' a => .success it' <|
    (it.toString.toSubstring.extract it.pos it'.pos, a)
  | .error it' e  => .error it' e

@[inline] def extractSub (p : Parsec α) : Parsec Substring :=
  (·.1) <$> withSubstring p

@[macro_inline] def orelse (p1 p2 : Parsec α) : Parsec α :=
  (attempt p1) <|> p2

@[inline] def andthen (p1 : Parsec α) (p2 : Parsec β) : Parsec (α × β) := do
  return (← p1, ← p2)

@[macro_inline] partial def skipSatisfy
(pred : Char → Bool) (errMsg := "condition not satisfied") : Parsec PUnit := do
  unless pred (← anyChar) do fail errMsg

@[inline] partial def skipMany (p : Parsec α) : Parsec PUnit := do
  if (← matched p) then skipMany p else pure ()

@[macro_inline] def skipMany1 (p : Parsec α) : Parsec PUnit :=
  discard p *> skipMany p

@[inline] def bit : Parsec Char := attempt do
  let c ← anyChar; if c = '0' ∨ c ≤ '1' then return c else fail s!"bit expected"

@[inline] def octDigit : Parsec Char := attempt do
  let c ← anyChar; if '0' ≤ c ∧ c ≤ '7' then return c else fail s!"octal digit expected"

@[inline] def nop : Parsec PUnit := pure ()
