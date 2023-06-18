/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Syntax
import Lean.Message
import Lean.Parser.Extension
import Partax.Parsec.Basic

open Lean hiding Parsec

namespace Partax

--------------------------------------------------------------------------------
-- # Parsec Type for Parsing Syntax
--------------------------------------------------------------------------------

export Lean.Parser (InputContext Error)

structure ParsecContext extends InputContext where
  prec : Nat
  savedPos? : Option String.Pos := none

structure ParsecState where
  lhsPrec : Nat := 0
  pos : String.Pos := 0

abbrev Parsec := ReaderT ParsecContext <| EStateM Error ParsecState

namespace Parsec

instance : MonadInput Parsec where
  getInput := return (← read).input
  getInputPos := return (← get).pos
  setInputPos pos := modify ({· with pos := pos})

instance : MonadCheckpoint Parsec where
  checkpoint f := fun c s => let d := s; f (fun _ _ => .ok () d) c s

instance : ThrowUnexpected Parsec where
  throwUnexpected unexpected expected := throw {unexpected, expected}

def mergeOrElse (p1 : Parsec α) (p2 : Unit → Parsec α) : Parsec α :=
  try p1 catch e1 => try p2 () catch e2 => throw <| e1.merge e2

instance : MonadOrElse Parsec := ⟨mergeOrElse⟩

open Lean Parser in
@[inline] nonrec def run (p : Parsec α) (input : String) : Except String α :=
  let ctx := {toInputContext := mkInputContext input "<string>", prec := 0}
  match p.run ctx |>.run {} with
  | .ok a _ => .ok a
  | .error e s =>
    let pos := ctx.fileMap.toPosition s.pos
    .error <| mkErrorStringWithPos ctx.fileName pos (toString e)

@[inline] def fail (errMsg : String := "parse failure") : Parsec α := do
  throw {unexpected := errMsg}

@[always_inline, inline] def nop : Parsec PUnit := pure ()

def throwUnexpectedPrec : Parsec PUnit :=
  throwUnexpected "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def checkPrec (prec : Nat) : Parsec PUnit := do
  unless (← read).prec ≤ prec do throwUnexpectedPrec

@[inline] def withPrec (prec : Nat) (p : Parsec α) : Parsec α := do
  withReader ({· with prec}) p

@[inline] def checkLhsPrec (prec : Nat) : Parsec PUnit := do
  unless (← get).lhsPrec ≤ prec do throwUnexpectedPrec

@[inline] def setLhsPrec (prec : Nat) : Parsec PUnit := do
  modify ({· with lhsPrec := prec})

@[inline] def withSavedPos (savedPos? : Option String.Pos) (p : Parsec α) : Parsec α := do
  withReader ({· with savedPos?}) p

@[inline] def withPosition (p : Parsec α) : Parsec α := do
  withSavedPos (← getInputPos) p

@[inline] def withoutPosition (p : Parsec α) : Parsec α := do
  withSavedPos none p

@[inline] def compareToSavedPos (f : Position → Position → Bool) (errorMsg : String) : Parsec PUnit := do
  let ctx ← read
  if let some savedPos := ctx.savedPos? then
    let savedPos := ctx.fileMap.toPosition savedPos
    let pos := ctx.fileMap.toPosition (← getInputPos)
    unless f pos savedPos do throwUnexpected errorMsg

@[inline] def checkColGe (errorMsg : String := "checkColGe") : Parsec PUnit := do
  compareToSavedPos (·.column ≥ ·.column) errorMsg

@[inline] def checkColGt (errorMsg : String := "checkColGt") : Parsec PUnit := do
  compareToSavedPos (·.column > ·.column) errorMsg

@[inline] def checkColEq (errorMsg : String := "checkColEq") : Parsec PUnit := do
  compareToSavedPos (·.column = ·.column) errorMsg

@[inline] def checkLinebreakBefore : Parsec PUnit := do
  nop -- TODO: stub

--------------------------------------------------------------------------------
-- # Syntax-specific Parsers
--------------------------------------------------------------------------------

instance : CoeOut (Parsec Syntax) (Parsec (Array Syntax)) where
  coe x := Array.singleton <$> x

instance : CoeOut (Parsec (Array (TSyntax k))) (Parsec (Array Syntax)) where
  coe x := x

instance : CoeOut (Parsec (TSyntax k)) (Parsec Syntax) where
  coe x := x

def withSourceInfo (p : Parsec α) : Parsec (SourceInfo × α) := do
  let leading ← extractSub skipWs
  let start ← getInputPos
  let a ← p
  let stop ← getInputPos
  let trailing ← extractSub skipWs
  let info := .original leading start trailing stop
  return (info, a)

def stdId : Parsec String := do
  extract do
    skipSatisfy isIdFirst ["identifier start"]
    skipMany1 <| skipSatisfy isIdRest ["identifier part"]

def atomicId : Parsec String := do
  if (← attempt <| satisfy isIdBeginEscape) then
    extract do skipTillSatisfy isIdEndEscape
  else
    let id ← extract do
      skipSatisfy isIdFirst ["identifier start"]
      skipMany1 <| skipSatisfy isIdRest ["identifier part"]
    if id = "_" then throwUnexpected "hole" ["ident"]
    return id

def name : Parsec Name := do
  let mut n := Name.anonymous
  repeat
    let s ← atomicId
    n := Name.str n s
  until !(← attempt <| skipChar '.')
  return n

def ident : Parsec Ident := do
  let (info, rawVal, val) ← atomic <| withSourceInfo <| withSubstring <| name
  return ⟨.ident info rawVal val []⟩

def atomOf (p : Parsec PUnit) : Parsec Syntax := do
  let (info, val) ← atomic <| withSourceInfo <| extract p
  return .atom info val

abbrev TAtom (val : String) := TSyntax (Name.str .anonymous val)

def atom (val : String) : Parsec (TAtom val) :=
  (⟨·⟩) <$> atomOf (skipString val)

def node (kind : SyntaxNodeKind) (p : Parsec (Array Syntax)) : Parsec (TSyntax kind) := do
  return ⟨.node SourceInfo.none kind (← p)⟩

def leadingNode (kind : SyntaxNodeKind) (prec : Nat) (p : Parsec (Array Syntax)) : Parsec (TSyntax kind) := do
  checkPrec prec; let n ← node kind p; setLhsPrec prec; return n

def trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : Parsec (Array Syntax)) : Parsec (TSyntax kind) := do
  checkPrec prec; checkLhsPrec lhsPrec; let n ← node kind p; setLhsPrec prec; return n

def group (p : Parsec (Array Syntax)) : Parsec Syntax :=
  node groupKind p

def hole : Parsec (TSyntax `Lean.Parser.Term.hole) :=
  node `Lean.Parser.Term.hole <| atom "_"

def num : Parsec NumLit :=
  node numLitKind <| Array.singleton <$> atomOf do
    let c ← digit
    if c = '0' then
      let b ← anyChar
      match b with
      | 'b' => skipMany1 hexDigit
      | 'o' => skipMany1 octDigit
      | 'x' => skipMany1 bit
      | _ => skipMany digit
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

def optional (p : Parsec (Array Syntax)) : Parsec Syntax :=
  attemptD mkNullNode <| @mkNullNode <$> p

def manySyntax (p : Parsec Syntax) : Parsec Syntax :=
  @mkNullNode <$> many p

def many1Syntax (p : Parsec Syntax) : Parsec Syntax :=
  @mkNullNode <$> many1 p

def sepByTrailing (initArgs : Array Syntax)
(p : Parsec Syntax) (sep : Parsec Syntax) : Parsec Syntax := do
  let mut args := initArgs
  repeat if let some a ← attempt? p then
    args := args.push a
    if let some s ← attempt? sep then
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
    if let some s ← attempt? sep then
      args := args.push s
    else
      break
  return mkNullNode args

def sepBy (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep : Bool) : Parsec Syntax := do
  if allowTrailingSep then
    sepByTrailing #[] p sep
  else if let some a ← attempt? p then
    if let some s ← attempt? sep then
      sepBy1NoTrailing #[a, s] p sep
    else
      return mkNullNode #[a]
  else
    return mkNullNode

def sepBy1 (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep : Bool) : Parsec Syntax := do
  let a ← p
  if let some s ← attempt? sep then
    if allowTrailingSep then
      sepByTrailing #[a, s] p sep
    else
      return mkNullNode #[a]
  else
    sepBy1NoTrailing #[] p sep

@[inline] def sepByIndent (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep := false) : Parsec Syntax :=
  withPosition <| sepBy (checkColGe *> p) (sep <|> checkColEq *> checkLinebreakBefore *> pure mkNullNode) allowTrailingSep

@[inline] def sepBy1Indent (p : Parsec Syntax) (sep : Parsec Syntax) (allowTrailingSep := false) : Parsec Syntax :=
  withPosition <| sepBy1 (checkColGe *> p) (sep <|> checkColEq *> checkLinebreakBefore *> pure mkNullNode) allowTrailingSep

def sepByIndentSemicolon (p : Parsec Syntax) : Parsec Syntax :=
  sepByIndent p (atom ";") (allowTrailingSep := true)

def sepBy1IndentSemicolon (p : Parsec Syntax) : Parsec Syntax :=
  sepBy1Indent p (atom ";") (allowTrailingSep := true)

-- Only a trivial replication (no pratt parsing)
def category (name : Name) (kinds : Array (Parsec Syntax)) : Parsec (TSyntax name) := do
  (⟨·⟩) <$> choice kinds s!"attempted to parse empty category '{name}'"

-- Just for testing purposes

def term : Parsec Term :=
  category `term #[ident, num, str]

def decimal : Parsec Syntax := atomOf do
  skipMany digit

end Parsec

--------------------------------------------------------------------------------
-- ## Combinator Classes
--------------------------------------------------------------------------------

instance : Append SyntaxNodeKinds := inferInstanceAs (Append (List SyntaxNodeKind))

class ParsecOrElse (α : Type) (β : Type) (γ : outParam Type) where
  orElse : Parsec α → Parsec β → Parsec γ

instance : ParsecOrElse Syntax Syntax Syntax where
  orElse p1 p2 := p1 <|> p2

instance : ParsecOrElse (TSyntax k1) (TSyntax k2) (TSyntax (k1 ++ k2)) where
  orElse p1 p2 := ((⟨·.raw⟩) <$> p1) <|> ((⟨·.raw⟩)  <$> p2)

instance : ParsecOrElse (Array (TSyntax k1)) (TSyntax k2) (Array (TSyntax (k1 ++ k2))) where
  orElse p1 p2 := ((·.map (⟨·.raw⟩)) <$> p1) <|> ((Array.singleton ⟨·.raw⟩) <$> p2)

instance : ParsecOrElse (TSyntax k1) (Array (TSyntax k2)) (Array (TSyntax (k1 ++ k2))) where
  orElse p1 p2 := ((Array.singleton ⟨·.raw⟩) <$> p1) <|> ((·.map (⟨·.raw⟩)) <$> p2)

instance [ParsecOrElse α β γ] : HOrElse (Parsec α) (Parsec β) (Parsec γ) where
  hOrElse p1 p2 := ParsecOrElse.orElse p1 (p2 ())

class ParsecAndThen (α : Type) (β : Type) (γ : outParam Type) where
  andThen : Parsec α → Parsec β → Parsec γ

instance [ParsecAndThen α β γ] : HAndThen (Parsec α) (Parsec β) (Parsec γ) where
  hAndThen p1 p2 := ParsecAndThen.andThen p1 (p2 ())

instance : ParsecAndThen Syntax Syntax (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : ParsecAndThen (TSyntax k1) (TSyntax k2) (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : ParsecAndThen (Array Syntax) (Array Syntax) (Array Syntax) where
  andThen p1 p2 := return (← p1) ++ (← p2)

instance : ParsecAndThen (TSyntax k) Syntax (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : ParsecAndThen Syntax (TSyntax k) (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : ParsecAndThen (Array Syntax) (TSyntax k) (Array Syntax) where
  andThen p1 p2 := return (← p1).push (← p2)

instance : ParsecAndThen (TSyntax k) (Array Syntax) (Array Syntax) where
  andThen p1 p2 := return #[← p1] ++ (← p2)

instance : ParsecAndThen α PUnit α where
  andThen p1 p2 := do let r ← p1; p2; return r

instance : ParsecAndThen PUnit α α where
  andThen p1 p2 := do p1; p2
