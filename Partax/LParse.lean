/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Syntax
import Lean.Message
import Lean.Parser.Extension
import Partax.Basic

open Lean

namespace Partax

--------------------------------------------------------------------------------
-- # LParse Type for Parsing Syntax
--------------------------------------------------------------------------------

export Lean.Parser (InputContext Error)

abbrev FieldIdx := TSyntax fieldIdxKind
abbrev TAtom (val : String) := TSyntax (Name.mkSimple val)

structure LParseContext extends InputContext where
  prec : Nat
  savedPos? : Option String.Pos := none

structure LParseState where
  lhsPrec : Nat := 0
  pos : String.Pos := 0
  prevWs : Substring := "".toSubstring

/-- Combinatorial, monadic parser for Lean-style parsing. -/
abbrev LParse := ReaderT LParseContext <| EStateM Error LParseState

namespace LParse

instance : MonadInput LParse where
  getInput := return (← read).input
  getInputPos := return (← get).pos
  setInputPos pos := modify ({· with pos := pos})

instance : MonadCheckpoint LParse where
  checkpoint f := fun c s => let d := s; f (fun _ _ => .ok () d) c s

instance : MonadBacktrack LParseState LParse where
  saveState := fun _ s => .ok s s
  restoreState s := fun _ _ => .ok () s

instance : ThrowUnexpected LParse where
  throwUnexpected unexpected expected := throw {unexpected, expected}

@[inline] def mergeOrElse (p1 : LParse α) (p2 : Unit → LParse α) : LParse α :=
  try p1 catch e1 => try p2 () catch e2 => throw <| e1.merge e2

instance : MonadOrElse LParse := ⟨mergeOrElse⟩

@[inline] def consumeWs : LParse Substring := do
  let ws ← extractSub skipWs
  modify ({· with prevWs := ws})
  return ws

open Parser in
nonrec def run (p : LParse α)
(input : String) (fileName := "<string>") (rbp := 0) : Except String α :=
  let ctx := {toInputContext := mkInputContext input fileName, prec := rbp}
  match (consumeWs *> p <* checkEOI).run ctx |>.run {} with
  | .ok a _ => .ok a
  | .error e s =>
    let pos := ctx.fileMap.toPosition s.pos
    .error <| mkErrorStringWithPos ctx.fileName pos (toString e)

/--
A do-nothing parser for aliasing.
It is specialized to `LParse` for better type inference.
-/
@[always_inline, inline] def nop : LParse PUnit := pure ()

@[inline] def fail (errMsg : String := "parse failure") : LParse α := do
  throw {unexpected := errMsg}

@[noinline] def unexpectedPrecMessage : String :=
  "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def throwUnexpectedPrec : LParse PUnit :=
  throwUnexpected unexpectedPrecMessage

@[inline] def checkPrec (prec : Nat) : LParse PUnit := do
  unless (← read).prec ≤ prec do throwUnexpectedPrec

@[inline] def withPrec (prec : Nat) (p : LParse α) : LParse α := do
  withReader ({· with prec}) p

@[inline] def checkLhsPrec (prec : Nat) : LParse PUnit := do
  unless (← get).lhsPrec ≥ prec do throwUnexpectedPrec

@[inline] def setLhsPrec (prec : Nat) : LParse PUnit := do
  modify ({· with lhsPrec := prec})

@[inline] def getWsBefore : LParse Substring := (·.prevWs) <$> get

@[inline] def checkWsBefore (errorMsg : String := "space before") : LParse PUnit := do
  if (← getWsBefore).isEmpty then fail errorMsg

@[inline] def checkNoWsBefore (errorMsg : String := "no space before") : LParse PUnit := do
  unless (← getWsBefore).isEmpty do fail errorMsg

@[inline] def checkLinebreakBefore (errorMsg : String := "line break") : LParse PUnit := do
  unless (← getWsBefore).contains '\n' do fail errorMsg

@[inline] def withSavedPos (savedPos? : Option String.Pos) (p : LParse α) : LParse α := do
  withReader ({· with savedPos?}) p

@[inline] def withPosition (p : LParse α) : LParse α := do
  withSavedPos (← getInputPos) p

@[inline] def withPositionAfterLinebreak (p : LParse α) : LParse α  := do
  if (← getWsBefore).contains '\n' then withPosition p else p

@[inline] def withoutPosition (p : LParse α) : LParse α := do
  withSavedPos none p

@[inline] def errorAtSavedPos (msg : String) (delta : Bool) : LParse PUnit := do
  if let some pos := (← read).savedPos? then
    setInputPos <| if delta then (← getInput).next pos else pos
    throwUnexpected msg

@[inline] def compareToSavedPos (f : Position → Position → Bool) (errorMsg : String) : LParse PUnit := do
  let ctx ← read
  if let some savedPos := ctx.savedPos? then
    let savedPos := ctx.fileMap.toPosition savedPos
    let pos := ctx.fileMap.toPosition (← getInputPos)
    unless f pos savedPos do throwUnexpected errorMsg

@[inline] def checkColGe (errorMsg : String := "checkColGe") : LParse PUnit := do
  compareToSavedPos (·.column ≥ ·.column) errorMsg

@[inline] def checkColGt (errorMsg : String := "checkColGt") : LParse PUnit := do
  compareToSavedPos (·.column > ·.column) errorMsg

@[inline] def checkColEq (errorMsg : String := "checkColEq") : LParse PUnit := do
  compareToSavedPos (·.column = ·.column) errorMsg

@[inline] def checkLineEq (errorMsg : String := "checkLineEq") : LParse PUnit := do
  compareToSavedPos (·.line = ·.line) errorMsg

--------------------------------------------------------------------------------
-- # Syntax-specific Parsers
--------------------------------------------------------------------------------

instance : CoeOut (LParse Syntax) (LParse (Array Syntax)) where
  coe x := Array.singleton <$> x

instance : CoeOut (LParse (Array (TSyntax k))) (LParse (Array Syntax)) where
  coe x := x

instance : CoeOut (LParse (TSyntax k)) (LParse Syntax) where
  coe x := x

/- Like Lean, assumes all leading whitespace has already been consumed. -/
def withSourceInfo (p : LParse α) : LParse (SourceInfo × α) := do
  let start ← getInputPos
  let leading : Substring :=
    {str := ← getInput, startPos := (← getWsBefore).stopPos, stopPos := start}
  let a ← p
  let stop ← getInputPos
  let trailing ← consumeWs
  let info := .original leading start trailing stop
  return (info, a)

def atomicIdent : LParse String := do
  if (← attempt <| satisfy isIdBeginEscape) then
    extract do skipTillSatisfy isIdEndEscape
  else
    let id ← extract do
      skipSatisfy isIdFirst ["ident"]
      skipMany <| skipSatisfy isIdRest
    if id = "_" then throwUnexpected "hole" ["ident"]
    return id

def name : LParse Name := do
  let mut n := Name.anonymous
  repeat
    let s ← atomicIdent
    n := Name.str n s
  until !(← attempt <| skipChar '.')
  return n

def ident : LParse Ident := do
  let (info, rawVal, val) ← atomic <| withSourceInfo <| withSubstring <| name
  return ⟨.ident info rawVal val []⟩

def atomOf (p : LParse PUnit) : LParse Syntax := do
  let (info, val) ← atomic <| withSourceInfo <| extract p
  return .atom info val

def atom (val : String) : LParse (TAtom val) :=
  (⟨·⟩) <$> atomOf (skipString val)

def rawCh (c : Char) (trailingWs := false) : LParse (TAtom c.toString) := do
  let input ← getInput
  let start ← getInputPos
  let leading : Substring :=
    {str := input, startPos := (← getWsBefore).stopPos, stopPos := start}
  skipChar c
  let stop ← getInputPos
  let trailing := if trailingWs then (← consumeWs) else
    {str := input, startPos := stop, stopPos := stop}
  let info := .original leading start trailing stop
  return ⟨.atom info c.toString⟩

@[inline] def symbol (sym : String) : LParse (TAtom sym.trim) :=
  atom sym.trim

@[inline] def nonReservedSymbol (sym : String) (_includeIdent := false) : LParse (TAtom sym.trim) :=
  atom sym.trim

def unicodeSymbol (sym asciiSym : String) : LParse Syntax :=
  atomOf (skipString sym.trim <|> skipString asciiSym.trim)

def node (kind : SyntaxNodeKind) (p : LParse (Array Syntax)) : LParse (TSyntax kind) := do
  return ⟨.node SourceInfo.none kind (← p)⟩

def leadingNode (kind : SyntaxNodeKind) (prec : Nat) (p : LParse (Array Syntax)) : LParse (TSyntax kind) := do
  checkPrec prec; let n ← node kind p; setLhsPrec prec; return n

def trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : LParse (Array Syntax)) : LParse (TSyntax kind) := do
  checkPrec prec; checkLhsPrec lhsPrec; let n ← node kind p; setLhsPrec prec; return n

def group (p : LParse (Array Syntax)) : LParse Syntax :=
  node groupKind p

def hole : LParse (TSyntax `Lean.Parser.Term.hole) :=
  node `Lean.Parser.Term.hole <| atom "_"

def fieldIdx : LParse FieldIdx :=
  node fieldIdxKind <| Array.singleton <$> atomOf do
    skipSatisfy fun c => '1' ≤ c ∧ c ≤ '9'
    skipMany digit

def strLit : LParse StrLit :=
  node strLitKind <| Array.singleton <$> atomOf do
    skipChar '"'
    repeat
      match (← anyChar) with
      | '\\' => skip
      | '"' => break
      | _ => continue

def charLit : LParse CharLit :=
  node charLitKind <| Array.singleton <$> atomOf do
    skipChar '\''
    if (← anyChar) = '\\' then
      skipSatisfy Parser.isQuotableCharDefault
    skipChar '\''

def numLit : LParse NumLit :=
  node numLitKind <| Array.singleton <$> atomOf do
    let c ← digit
    if c = '0' then
      let b ← peek
      match b with
      | 'b' => skipMany1 hexDigit
      | 'o' => skipMany1 octDigit
      | 'x' => skipMany1 bit
      | _ => skipMany1 digit
    else
      skipMany digit

def scientificLit : LParse ScientificLit :=
  node scientificLitKind <| Array.singleton <$> atomOf do
    skipMany1 digit
    let expected := ["'.'", "'e'", "'E'"]
    let c ← anyChar expected
    if c == '.' then
      skipMany1 digit
    else if c == 'e' || c == 'E' then
      skipIfSatisfy fun c => c == '-' || c == '+'
      skipMany1 digit
    else
      throwUnexpected s!"unexpected '{c}'" expected

def nameLit : LParse NameLit :=
  node nameLitKind <| Array.singleton <$> atomOf do
    skipChar '`'; discard name

def optional (p : LParse (Array Syntax)) : LParse Syntax :=
  attemptD mkNullNode <| @mkNullNode <$> p

def many (p : LParse Syntax) : LParse Syntax :=
  @mkNullNode <$> collectMany p

def many1 (p : LParse Syntax) : LParse Syntax :=
  @mkNullNode <$> collectMany1 p

def many1Unbox (p : LParse Syntax) : LParse Syntax :=
  collectMany1 p <&> fun xs =>
    if _ : xs.size = 1 then xs[0]'(by simp [*]) else mkNullNode xs

def sepByTrailing (initArgs : Array Syntax)
(p : LParse Syntax) (sep : LParse Syntax) : LParse Syntax := do
  let mut args := initArgs
  repeat if let some a ← attempt? p then
    args := args.push a
    if let some s ← attempt? sep then
      args := args.push s
    else
      break
  return mkNullNode args

def sepBy1NoTrailing (initArgs : Array Syntax)
(p : LParse Syntax) (sep : LParse Syntax) : LParse Syntax := do
  let mut args := initArgs
  repeat
    let a ← p
    args := args.push a
    if let some s ← attempt? sep then
      args := args.push s
    else
      break
  return mkNullNode args

def sepBy (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep : Bool) : LParse Syntax := do
  if allowTrailingSep then
    sepByTrailing #[] p psep
  else if let some a ← attempt? p then
    if let some s ← attempt? psep then
      sepBy1NoTrailing #[a, s] p psep
    else
      return mkNullNode #[a]
  else
    return mkNullNode

def sepBy1 (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep : Bool) : LParse Syntax := do
  let a ← p
  if let some s ← attempt? psep then
    if allowTrailingSep then
      sepByTrailing #[a, s] p psep
    else
      return mkNullNode #[a]
  else
    sepBy1NoTrailing #[] p psep

@[inline] def pushNone : LParse Syntax :=
  pure mkNullNode

@[inline] def sepByIndent (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax :=
  withPosition <| sepBy (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

@[inline] def sepBy1Indent (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax :=
  withPosition <| sepBy1 (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

def sepByIndentSemicolon (p : LParse Syntax) : LParse Syntax :=
  sepByIndent p ";" (allowTrailingSep := true)

def sepBy1IndentSemicolon (p : LParse Syntax) : LParse Syntax :=
  sepBy1Indent p ";" (allowTrailingSep := true)

@[inline] partial def trailingLoop (head : Syntax)
(trailing : Array (LParse Syntax)) (h : trailing.size > 0) : LParse Syntax :=
  step head
where
  step head := do
    let iniPos ← getInputPos
    checkpoint fun restore => do
    match (← observing <| longestMatch trailing h Parser.Error.merge) with
    | .ok tail =>
      let node := (.node .none tail.getKind <| #[head] ++ tail.getArgs)
      -- break the loop if a successful trailing parser does not consume anything
      if iniPos = (← getInputPos) then return node else step node
    | .error e =>
      if iniPos < (← getInputPos) then throw e else restore; return head

/-- Pratt parse a category with the given `leading` and `trailing` parsers. -/
def category (name : Name) (leading trailing : Array (LParse Syntax)) : LParse (TSyntax name) := do
  if h : leading.size > 0 then
    let head ← longestMatch leading h Parser.Error.merge
    if h : trailing.size > 0 then
      (⟨·⟩) <$> trailingLoop head trailing h
    else
      return ⟨head⟩
  else
    throwUnexpected s!"attempted to parse category '{name}' with no leading parsers"

end LParse

--------------------------------------------------------------------------------
-- ## Combinator Classes
--------------------------------------------------------------------------------

instance : Append SyntaxNodeKinds := inferInstanceAs (Append (List SyntaxNodeKind))

class LParseOrElse (α : Type) (β : Type) (γ : outParam Type) where
  orElse : LParse α → LParse β → LParse γ

instance : LParseOrElse Syntax Syntax Syntax where
  orElse p1 p2 := p1 <|> p2

instance : LParseOrElse (TSyntax k) Syntax Syntax where
  orElse p1 p2 := p1 <|> p2

instance : LParseOrElse Syntax (TSyntax k) Syntax where
  orElse p1 p2 := p1 <|> p2

instance : LParseOrElse (TSyntax k1) (TSyntax k2) (TSyntax (k1 ++ k2)) where
  orElse p1 p2 := ((⟨·.raw⟩) <$> p1) <|> ((⟨·.raw⟩)  <$> p2)

instance : LParseOrElse (Array (TSyntax k1)) (TSyntax k2) (Array (TSyntax (k1 ++ k2))) where
  orElse p1 p2 := ((·.map (⟨·.raw⟩)) <$> p1) <|> ((Array.singleton ⟨·.raw⟩) <$> p2)

instance : LParseOrElse (TSyntax k1) (Array (TSyntax k2)) (Array (TSyntax (k1 ++ k2))) where
  orElse p1 p2 := ((Array.singleton ⟨·.raw⟩) <$> p1) <|> ((·.map (⟨·.raw⟩)) <$> p2)

instance [LParseOrElse α β γ] : HOrElse (LParse α) (LParse β) (LParse γ) where
  hOrElse p1 p2 := LParseOrElse.orElse p1 (p2 ())

class LParseAndThen (α : Type) (β : Type) (γ : outParam Type) where
  andThen : LParse α → LParse β → LParse γ

instance [LParseAndThen α β γ] : HAndThen (LParse α) (LParse β) (LParse γ) where
  hAndThen p1 p2 := LParseAndThen.andThen p1 (p2 ())

instance : LParseAndThen Syntax Syntax (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : LParseAndThen (TSyntax k1) (TSyntax k2) (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : LParseAndThen (Array Syntax) (Array Syntax) (Array Syntax) where
  andThen p1 p2 := return (← p1) ++ (← p2)

instance : LParseAndThen (TSyntax k) Syntax (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : LParseAndThen Syntax (TSyntax k) (Array Syntax) where
  andThen p1 p2 := return #[(← p1), (← p2)]

instance : LParseAndThen (Array Syntax) (TSyntax k) (Array Syntax) where
  andThen p1 p2 := return (← p1).push (← p2)

instance : LParseAndThen (TSyntax k) (Array Syntax) (Array Syntax) where
  andThen p1 p2 := return #[← p1] ++ (← p2)

instance : LParseAndThen (Array Syntax) Syntax (Array Syntax) where
  andThen p1 p2 := return (← p1).push (← p2)

instance : LParseAndThen Syntax (Array Syntax) (Array Syntax) where
  andThen p1 p2 := return #[← p1] ++ (← p2)

instance : LParseAndThen α PUnit α where
  andThen p1 p2 := do let r ← p1; p2; return r

instance : LParseAndThen PUnit α α where
  andThen p1 p2 := do p1; p2
