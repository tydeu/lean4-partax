/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Syntax
import Partax.Parsec.Basic

open Lean Parsec Syntax

namespace Partax.Parsec

--------------------------------------------------------------------------------
-- # Syntax-specific Parsec Helpers
--------------------------------------------------------------------------------

instance : CoeOut (Parsec (TSyntax k)) (Parsec Syntax) where
  coe x := x

instance : Coe (Parsec Syntax) (Parsec (Array Syntax)) where
  coe x := Array.singleton <$> x

instance : CoeOut (Parsec (Array (TSyntax k))) (Parsec (Array Syntax)) where
  coe x := x

def withWsInfo (p : Parsec α) : Parsec (SourceInfo × α) := do
  let leading ← extractSub ws
  let start ← read
  let a ← p
  let stop ← read
  let trailing ← extractSub ws
  let info := .original leading start.pos trailing stop.pos
  return (info, a)

def atomicId : Parsec String := do
  if (← matched <| satisfy isIdBeginEscape) then
    extract do repeat if (← matched <| satisfy isIdEndEscape) then break
  else
    extract do
      skipSatisfy isIdFirst
      skipMany <| skipSatisfy isIdRest

def name : Parsec Name := do
  let mut n := Name.anonymous
  repeat
    let s ← atomicId
    n := Name.str n s
  until !(← matched <| skipChar '.')
  return n

def ident : Parsec Ident := do
  let (info, rawVal, val) ← withWsInfo <| withSubstring <| name
  return ⟨.ident info rawVal val []⟩

def atomOf (p : Parsec PUnit) : Parsec Syntax := do
  let (info, val) ← withWsInfo <| extract p
  return .atom info val

abbrev TAtom (val : String) := TSyntax (Name.str .anonymous val)

def atom (val : String) : Parsec (TAtom val) :=
  (⟨·⟩) <$> atomOf (skipString val)

def decimal : Parsec Syntax := atomOf do
  skipMany digit

def node (kind : SyntaxNodeKind) (p : Parsec (Array Syntax)) : Parsec (TSyntax kind) := do
  return ⟨.node SourceInfo.none kind (← p)⟩

def hole : Parsec (TSyntax `Lean.Parser.Term.hole) :=
  node `Lean.Parser.Term.hole <| atom "_"

def num : Parsec NumLit :=
  node numLitKind <| Array.singleton <$> atomOf do
    let c ← digit
    if c = '0' then
      match (← anyChar) with
      | 'b' => skipMany1 hexDigit
      | 'o' => skipMany1 octDigit
      | 'x' => skipMany1 bit
      | _ => fail "numeral expected"
    else
      skipMany digit

def str : Parsec StrLit :=
  node strLitKind <| Array.singleton <$> atomOf do
    skipChar '"'
    repeat
      match (← anyChar) with
      | '\\' => skip
      | '"' => break
      | _ => continue

def optional (p : Parsec (Array Syntax)) : Parsec Syntax := fun it =>
  match p it with
  | .success it args => .success it (mkNullNode args)
  | .error _ _ => .success it mkNullNode

def sepByTrailing (initArgs : Array Syntax)
(p : Parsec Syntax) (sep : Parsec Syntax) : Parsec Syntax := do
  let mut args := initArgs
  repeat if let some a ← option p then
    args := args.push a
    if let some s ← option sep then
      args := args.push s
    else
      break
  return mkNullNode args

def sepBy1NoTrailing (initArgs : Array Syntax)
(p : Parsec Syntax) (sep : Parsec Syntax) : Parsec Syntax := do
  let mut args := initArgs
  repeat
    let a ← p
    args := args.push a
    if let some s ← option sep then
      args := args.push s
    else
      break
  return mkNullNode args

def sepBy (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep : Bool) : Parsec Syntax := do
  if allowTrailingSep then
    sepByTrailing #[] p sep
  else if let some a ← option p then
    if let some s ← option sep then
      sepBy1NoTrailing #[a, s] p sep
    else
      return mkNullNode #[a]
  else
    return mkNullNode

def sepBy1 (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep : Bool) : Parsec Syntax := do
  let a ← p
  if let some s ← option sep then
    if allowTrailingSep then
      sepByTrailing #[a, s] p sep
    else
      return mkNullNode #[a]
  else
    sepBy1NoTrailing #[] p sep

-- Only a trivial replication (no pratt parsing)
def cat (name : Name) (kinds : Array (Parsec Syntax)) : Parsec (TSyntax name) := do
  (⟨·⟩) <$> kinds.foldr orelse (fail "")

-- Just for testing purposes
def term : Parsec Term :=
  cat `term #[ident, num, str]

--------------------------------------------------------------------------------
-- ## Parsec Combinators
--------------------------------------------------------------------------------

class OrElse (α : Type) (β : Type) (γ : outParam Type) where
  pOrElse : Parsec α → Parsec β → Parsec γ

instance : OrElse Syntax Syntax Syntax where
  pOrElse p1 p2 := orelse p1 p2

instance : Append SyntaxNodeKinds := inferInstanceAs (Append (List SyntaxNodeKind))

instance : OrElse (TSyntax k1) (TSyntax k2) (TSyntax (k1 ++ k2)) where
  pOrElse p1 p2 := orelse ((⟨·.raw⟩) <$> p1) ((⟨·.raw⟩)  <$> p2)

instance : OrElse (Array (TSyntax k1)) (TSyntax k2) (Array (TSyntax (k1 ++ k2))) where
  pOrElse p1 p2 := orelse
    ((·.map (⟨·.raw⟩)) <$> p1)
    ((fun x => Array.singleton ⟨x.raw⟩) <$> p2)

instance : OrElse (TSyntax k1) (Array (TSyntax k2)) (Array (TSyntax (k1 ++ k2))) where
  pOrElse p1 p2 := orelse
    ((fun x => Array.singleton ⟨x.raw⟩) <$> p1)
    ((·.map (⟨·.raw⟩)) <$> p2)

class AndThen (α : Type) (β : Type) (γ : outParam Type) where
  pAndThen : Parsec α → Parsec β → Parsec γ

instance : AndThen (Array Syntax) (Array Syntax) (Array Syntax) where
  pAndThen p1 p2 := return (← p1) ++ (← p2)

instance : AndThen (Array (TSyntax k1)) (Array (TSyntax k2)) (Array Syntax) where
  pAndThen p1 p2 := return (← p1) ++ (← p2)

instance : AndThen (Array (TSyntax k)) (Array Syntax) (Array Syntax) where
  pAndThen p1 p2 := return (← p1) ++ (← p2)

instance : AndThen (Array Syntax) (Array (TSyntax k)) (Array Syntax) where
  pAndThen p1 p2 := return (← p1) ++ (← p2)

instance : AndThen (Array Syntax) (TSyntax k) (Array Syntax) where
  pAndThen p1 p2 := return (← p1).push (← p2)

instance : AndThen (TSyntax k) (Array Syntax) (Array Syntax) where
  pAndThen p1 p2 := return #[← p1] ++ (← p2)

instance : AndThen (Array (TSyntax k1)) (TSyntax k2) (Array Syntax) where
  pAndThen p1 p2 := return ((← p1) : Array Syntax).push (← p2)

instance : AndThen (TSyntax k1) (Array (TSyntax k2))  (Array Syntax) where
  pAndThen p1 p2 := return #[← p1] ++ (← p2)

instance : AndThen (Array Syntax) Syntax (Array Syntax) where
  pAndThen p1 p2 := return (← p1).push (← p2)

instance : AndThen (Array (TSyntax k)) Syntax (Array Syntax) where
  pAndThen p1 p2 := return ((← p1) : Array Syntax).push (← p2)

instance : AndThen Syntax Syntax (Array Syntax) where
  pAndThen p1 p2 := return #[(← p1), (← p2)]

instance : AndThen (TSyntax k1) (TSyntax k2) (Array Syntax) where
  pAndThen p1 p2 := return #[(← p1), (← p2)]

instance : AndThen (TSyntax k) Syntax (Array Syntax) where
  pAndThen p1 p2 := return #[(← p1), (← p2)]

instance : AndThen Syntax (TSyntax k) (Array Syntax) where
  pAndThen p1 p2 := return #[(← p1), (← p2)]

instance : AndThen α PUnit α where
  pAndThen p1 p2 := do let r ← p1; p2; return r

instance : AndThen PUnit α α where
  pAndThen p1 p2 := do p1; p2
