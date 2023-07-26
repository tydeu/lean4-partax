/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Syntax
import Lean.Message
import Lean.Parser.Extension
import Partax.Basic

open Lean

namespace Partax

export Lean.Parser (InputContext Error)

abbrev FieldIdx := TSyntax fieldIdxKind
abbrev InterpolatedStr := TSyntax interpolatedStrKind

--------------------------------------------------------------------------------
-- # LParse Type for Parsing Syntax
--------------------------------------------------------------------------------

opaque OpaqueLParse.nonemptyType (α : Type u) : NonemptyType.{0}
/-- An opaque forward-declared version of `LParse` for wrapping category parsers. -/
def OpaqueLParse (α : Type α) : Type := OpaqueLParse.nonemptyType α |>.type
instance : Nonempty (OpaqueLParse α) :=  OpaqueLParse.nonemptyType α |>.property

abbrev SymbolTrie := Lean.Parser.Trie String
@[inline] def SymbolTrie.empty : SymbolTrie := {}
@[inline] def SymbolTrie.ofList (syms : List String) : SymbolTrie :=
  syms.foldl (init := {}) fun t s => t.insert s s

abbrev SymbolSet := RBTree String compare
@[inline] def SymbolSet.empty : SymbolSet := {}
@[inline] partial def SymbolTrie.toSet (trie : SymbolTrie) : SymbolSet :=
  go {} trie
where
  go s
  | .Node sym? map =>
    let s := if let some sym := sym? then s.insert sym else s
    map.fold (init := s) fun s _ t => go s t

abbrev ParserMap := NameMap (OpaqueLParse Syntax)
@[inline] def ParserMap.empty : ParserMap := {}
@[inline] def ParserMap.ofList (xs : List (Name × OpaqueLParse Syntax)) : ParserMap :=
  xs.foldl (init := {}) fun m (k, v) => m.insert k v
@[inline] def ParserMap.toSet (map : ParserMap) : NameSet :=
  map.fold (init := {}) fun s k _ => s.insert k

structure LParseContext extends InputContext where
  prec : Nat := 0
  savedPos? : Option String.Pos := none
  cats : ParserMap := {}
  kws : NameSet := {}
  forbiddenKw : Name := .anonymous
  syms : SymbolTrie := {}

structure LParseState where
  lhsPrec : Nat := 0
  inputPos : String.Pos := 0
  ignoredBefore : Substring := "".toSubstring

/-- Parser monadic transformer for Lean-style parsing. -/
abbrev LParseT (m) := ReaderT LParseContext <| ExceptT Error <| StateT LParseState m

/-- Combinatorial, monadic parser for Lean-style parsing. -/
abbrev LParse := ReaderT LParseContext <| EStateM Error LParseState

instance [Pure m] : MonadLift LParse (LParseT m) where
  monadLift x := fun r s =>
    match x r s with
    | .ok a s => pure (.ok a, s)
    | .error e s => pure (.error e, s)

namespace OpaqueLParse
unsafe def unsafeMk : LParse α → OpaqueLParse α := unsafeCast
@[implemented_by unsafeMk] opaque mk : LParse α → OpaqueLParse α
instance : Coe (LParse α) (OpaqueLParse α)  := ⟨mk⟩
instance : Inhabited (OpaqueLParse α) := ⟨mk default⟩
unsafe def unsafeGet : OpaqueLParse α → LParse α := unsafeCast
@[implemented_by unsafeGet] opaque get : OpaqueLParse α → LParse α
instance : Coe (OpaqueLParse α) (LParse α) := ⟨get⟩
end OpaqueLParse

class MonadIgnoredBefore (m : Type → Type u) where
  getIgnoredBefore : m Substring
  setIgnoredBefore : Substring → m PUnit

export MonadIgnoredBefore (getIgnoredBefore setIgnoredBefore)

instance [MonadLift m n] [MonadIgnoredBefore m] : MonadIgnoredBefore n where
  getIgnoredBefore := liftM (m := m) getIgnoredBefore
  setIgnoredBefore i := liftM (m := m) <| setIgnoredBefore i

namespace LParse
variable [Monad m] [MonadInput m] [ThrowUnexpected m]

@[specialize] partial def skipCommentBody : m Unit := do
  let rec loop (nesting : Nat) := do
    match (← next1) with
    | '-' =>
      if (← next1) = '/' then
        if nesting = 0 then
          return
        else
          loop (nesting-1)
      else
        loop nesting
    | '/' =>
      if (← next1) = '-' then
        loop (nesting+1)
      else
        loop nesting
    | _ => loop nesting
  loop 0

variable [MonadCheckpoint m] [MonadExcept ε m]

/-- Skip a single whitespace character or a comment. -/
@[specialize] def skipIgnoredToken : m Unit := atomic do
  match (← next1) with
  | '/' =>
    skipChar '-'
    skipSatisfy fun c => c ≠ '-' ∧ c ≠ '!'
    skipCommentBody
  | '-' =>
    skipChar '-'
    skipTillChar '\n'
  | c =>
    unless c.isWhitespace do
      throwUnexpected s!"unexpected '{c}'" ["whitespace", "comment"]

/-- Consumes whitespace and comments and saves them in the `LParseState`. -/
@[inline] def consumeIgnored [MonadIgnoredBefore m] : m Substring := do
  let ignored ← extractSub <| skipMany skipIgnoredToken
  setIgnoredBefore ignored
  return ignored

/-- Parse full input. Consumes initial ignored tokens and throws if input remains. -/
@[inline] def fullInput [MonadIgnoredBefore m] (p : m α) : m α := do
  consumeIgnored *> p <* checkEOI

end LParse

instance : MonadInput LParse where
  getInput := (·.input) <$> read
  getInputPos := (·.inputPos) <$> get
  setInputPos pos := modify ({· with inputPos := pos})

instance : MonadIgnoredBefore LParse where
  getIgnoredBefore := (·.ignoredBefore) <$> get
  setIgnoredBefore i := modify ({· with ignoredBefore := i})

instance : MonadBacktrack LParseState LParse where
  saveState := fun _ s => .ok s s
  restoreState s := fun _ _ => .ok () s

instance : ThrowUnexpected LParse where
  throwUnexpected unexpected expected := throw {unexpected, expected}

open Parser in
nonrec def LParse.run (input : String) (p : LParse α) (fileName := "<string>")
(rbp := 0) (cats : ParserMap := {}) (kws : NameSet := {}) (syms : SymbolTrie := {}) : Except String α :=
  let ictx := mkInputContext input fileName
  let ctx := {toInputContext := ictx, prec := rbp, cats, kws, syms}
  match (LParse.fullInput p : LParse α).run ctx |>.run {} with
  | .ok a _ => .ok a
  | .error e s =>
    let pos := ctx.fileMap.toPosition s.inputPos
    .error <| mkErrorStringWithPos ctx.fileName pos (toString e)

instance [Monad m]  : MonadInput (LParseT m) where
  getInput := (·.input) <$> read
  getInputPos := (·.inputPos) <$> get
  setInputPos pos := modify ({· with inputPos := pos})

instance [Monad m] : MonadIgnoredBefore (LParseT m) where
  getIgnoredBefore := (·.ignoredBefore) <$> get
  setIgnoredBefore i := modify ({· with ignoredBefore := i})

instance [Pure m] : MonadBacktrack LParseState (LParseT m) where
  saveState := fun _ s => pure (.ok s, s)
  restoreState s := fun _ _ => pure (.ok (), s)

open Parser in
nonrec def LParseT.run [Monad m] (input : String) (p : LParseT m α) (fileName := "<string>")
(rbp := 0) (cats : ParserMap := {}) (kws : NameSet := {}) (syms : SymbolTrie := {}) : ExceptT String m α := do
  let ictx := mkInputContext input fileName
  let ctx := {toInputContext := ictx, prec := rbp, cats, kws, syms}
  match (← (LParse.fullInput p : LParseT m α).run ctx |>.run.run {}) with
  | (.ok a, _) => pure a
  | (.error e, s) =>
    let pos := ctx.fileMap.toPosition s.inputPos
    throw <| mkErrorStringWithPos ctx.fileName pos (toString e)

namespace LParse

@[inline] def mergeOrElse (p1 : LParse α) (p2 : Unit → LParse α) : LParse α := do
  let s0 ← saveState
  try
    p1
  catch e1 =>
    let t1 := (← getInputPos).byteIdx
    let s1 ← saveAndRestoreState s0
    try
      p2 ()
    catch e2 =>
      let t2 := (← getInputPos).byteIdx
      match compare t1 t2 with
      | .lt => throw e2
      | .eq => restoreState s1; throw <| e1.merge e2
      | .gt => restoreState s1; throw e1

instance : MonadOrElse LParse := ⟨mergeOrElse⟩

/-- A do-nothing parser for aliasing. -/
@[always_inline, inline] def nop : LParse PUnit := pure ()

/- `LParse` specializations for better type inference. -/
protected abbrev atomic (p : LParse α) : LParse α := atomic p
protected abbrev lookahead (p : LParse α) : LParse PUnit := lookahead p
protected abbrev notFollowedBy (p : LParse α) (msg : String := "element") : LParse PUnit :=
  notFollowedBy p msg

@[inline] def error (msg : String := "parse failure") : LParse α := do
  throw {unexpected := msg}

@[noinline] def unexpectedPrecMessage : String :=
  "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def throwUnexpectedPrec : LParse PUnit :=
  throwUnexpected unexpectedPrecMessage

@[inline] def withForbiddenKeyword (kw : Name) (p : LParse α) : LParse α := do
  withReader ({· with forbiddenKw := kw}) p

@[inline] def withoutForbidden (p : LParse α) : LParse α := do
  withReader ({· with forbiddenKw := .anonymous}) p

@[inline] def withPrec (prec : Nat) (p : LParse α) : LParse α := do
  withReader ({· with prec}) p

@[inline] def checkPrec (prec : Nat) : LParse PUnit := do
  unless (← read).prec ≤ prec do throwUnexpectedPrec

@[inline] def checkLhsPrec (prec : Nat) : LParse PUnit := do
  unless (← get).lhsPrec ≥ prec do throwUnexpectedPrec

@[inline] def setLhsPrec (prec : Nat) : LParse PUnit := do
  modify ({· with lhsPrec := prec})

@[inline] def checkWsBefore (errorMsg : String := "space before") : LParse PUnit := do
  if (← getIgnoredBefore).isEmpty then error errorMsg

@[inline] def checkNoWsBefore (errorMsg : String := "no space before") : LParse PUnit := do
  unless (← getIgnoredBefore).isEmpty do error errorMsg

@[inline] def checkLinebreakBefore (errorMsg : String := "line break") : LParse PUnit := do
  unless (← getIgnoredBefore).contains '\n' do error errorMsg

@[inline] def withSavedPos (savedPos? : Option String.Pos) (p : LParse α) : LParse α := do
  withReader ({· with savedPos?}) p

@[inline] def withPosition (p : LParse α) : LParse α := do
  withSavedPos (← getInputPos) p

@[inline] def withPositionAfterLinebreak (p : LParse α) : LParse α  := do
  if (← getIgnoredBefore).contains '\n' then withPosition p else p

@[inline] def withoutPosition (p : LParse α) : LParse α := do
  withSavedPos none p

@[inline, inherit_doc Parser.errorAtSavedPos]
def errorAtSavedPos (msg : String) (delta : Bool) : LParse PUnit := do
  if let some pos := (← read).savedPos? then
    if delta then setInputPos <| (← getInput).next pos
    error msg

@[inline] def checkSavedPos (f : Position → Position → Bool) (errorMsg : String) : LParse PUnit := do
  let ctx ← read
  if let some savedPos := ctx.savedPos? then
    let savedPos := ctx.fileMap.toPosition savedPos
    let inputPos := ctx.fileMap.toPosition (← getInputPos)
    unless f inputPos savedPos do error errorMsg

@[inline] def checkColGe (errorMsg : String := "checkColGe") : LParse PUnit := do
  checkSavedPos (·.column ≥ ·.column) errorMsg

@[inline] def checkColGt (errorMsg : String := "checkColGt") : LParse PUnit := do
  checkSavedPos (·.column > ·.column) errorMsg

@[inline] def checkColEq (errorMsg : String := "checkColEq") : LParse PUnit := do
  checkSavedPos (·.column = ·.column) errorMsg

@[inline] def checkLineEq (errorMsg : String := "checkLineEq") : LParse PUnit := do
  checkSavedPos (·.line = ·.line) errorMsg

--------------------------------------------------------------------------------
-- # Syntax-specific Parsers
--------------------------------------------------------------------------------

instance : Coe (LParse PUnit) (LParse (Array Syntax)) where
  coe x := Functor.mapConst #[] x

instance : Coe (LParse Syntax) (LParse (Array Syntax)) where
  coe x := Array.singleton <$> x

instance : CoeOut (LParse (Array (TSyntax k))) (LParse (Array Syntax)) where
  coe x := x

instance : CoeOut (LParse (TSyntax k)) (LParse Syntax) where
  coe x := x

/- Like Lean, assumes all leading whitespace has already been consumed. -/
def withSourceInfo (p : LParse α) : LParse (SourceInfo × α) := do
  let start ← getInputPos
  let leading : Substring :=
    {str := ← getInput, startPos := (← getIgnoredBefore).stopPos, stopPos := start}
  let a ← p
  let stop ← getInputPos
  let trailing ← consumeIgnored
  let info := .original leading start trailing stop
  return (info, a)

def extractSourceInfo (p : LParse α) : LParse SourceInfo := do
  let (info, _) ← inline <| withSourceInfo p
  return info

def identAtom : LParse String := do
  if (← trySatisfy isIdBeginEscape) then
    let ident ← extract do
      skipToSatisfy isIdEndEscape ["end of identifier escape"]
    skip
    return ident
  else
    extract do
      skipSatisfy isIdFirst ["ident"]
      skipMany <| skipSatisfy isIdRest

partial def name : LParse Name := do
  let rec identCont (n : Name) := do
    if let some s ← attempt? <| atomic <| skipChar '.' *> identAtom then
      identCont (.str n s)
    else
      return n
  let s ← identAtom
  identCont (.str .anonymous s)

def ident : LParse Ident := do
  let (info, rawVal, val) ← atomic <| withSourceInfo <| withSubstring do
    let n ← name
    if (← read).kws.contains n then
      throwUnexpected s!"unexpected keyword '{n}'" ["ident"]
    else
      pure n
  return ⟨.ident info rawVal val []⟩

@[inline] def atomOf (p : LParse PUnit) : LParse Syntax := do
  let (info, val) ← atomic <| withSourceInfo <| extract p
  return .atom info val

@[inline] def atom (val : String) : LParse Syntax := do
  let info ← atomic <| extractSourceInfo <| skipString val
  return .atom info val

def rawCh (c : Char) (trailingWs := false) : LParse Syntax := do
  let input ← getInput
  let start ← getInputPos
  let leading : Substring :=
    {str := input, startPos := (← getIgnoredBefore).stopPos, stopPos := start}
  skipChar c
  let stop ← getInputPos
  let trailing := if trailingWs then (← consumeIgnored) else
    {str := input, startPos := stop, stopPos := stop}
  let info := .original leading start trailing stop
  return .atom info c.toString

@[inline] def keyword (kw : Name) : LParse Syntax :=
  atomOf do
    let n ← name
    if n = kw then
      if kw = (← read).forbiddenKw then
        error "forbidden keyword"
     else
      throwUnexpected "unexpected ident '{n}'" [s!"'{kw}'"]

def symbol (sym : String) : LParse Syntax := do
  let sym := sym.trim
  let info ← extractSourceInfo do
    let (newPos, nextSym?) :=
      (← read).syms.matchPrefix (← getInput) (← getInputPos)
    let expected := [s!"'{sym}'"]
    if let some nextSym := nextSym? then
      if sym = nextSym then
        setInputPos newPos
      else
        throwUnexpected s!"unexpected symbol '{nextSym}'" expected
    else
      throwUnexpected s!"unexpected non-symbol syntax" expected
  return .atom info sym

@[inline] def nonReservedSymbol (sym : String) (_includeIdent := false) : LParse Syntax :=
  atom sym.trim

def unicodeSymbol (sym asciiSym : String) : LParse Syntax :=
  atomOf (skipString sym.trim <|> skipString asciiSym.trim)

@[inline] def node (kind : SyntaxNodeKind) (p : LParse (Array Syntax)) : LParse (TSyntax kind) := do
  let args ← try p catch e => throw {e with unexpected := s!"{kind}: {e.unexpected}"}
  return ⟨.node .none kind args⟩

@[inline] def leadingNode (kind : SyntaxNodeKind) (prec : Nat) (p : LParse (Array Syntax)) : LParse (TSyntax kind) := do
  checkPrec prec; let n ← node kind p; setLhsPrec prec; return n

@[inline] def trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : LParse (Array Syntax)) : LParse (SyntaxNodeKind × Array Syntax) := do
  checkPrec prec; checkLhsPrec lhsPrec; let args ← p; setLhsPrec prec; return (kind, args)

@[inline] def group (p : LParse (Array Syntax)) : LParse Syntax :=
  node groupKind p

def commentBody : LParse Syntax :=
  atomOf skipCommentBody

def hygieneInfo : LParse HygieneInfo :=
  node hygieneInfoKind do
    let pos ← getInputPos
    let str : Substring :=
      {str := ← getInput, startPos := pos, stopPos := pos}
    let info := SourceInfo.original str pos str pos
    return #[.ident info str .anonymous []]

def fieldIdx : LParse FieldIdx :=
  node fieldIdxKind <| Array.singleton <$> atomOf do
    skipSatisfy fun c => '1' ≤ c ∧ c ≤ '9'
    skipMany digit

def skipEscapeSeq : LParse PUnit := do
  match (← next1) with
  | 'x' => discard hexDigit; discard hexDigit
  | 'u' => discard hexDigit; discard hexDigit; discard hexDigit; discard hexDigit
  | _ => pure ()

def charLit : LParse CharLit :=
  node charLitKind <| Array.singleton <$> atomOf do
    skipChar '\''
    if (← next1) = '\\' then skipEscapeSeq
    skipChar '\''

partial def strLit : LParse StrLit :=
  node strLitKind <| Array.singleton <$> atomOf do
    skipChar '"'
    let rec loop := do
      match (← next1) with
      | '\\' => skipEscapeSeq; loop
      | '"' => return
      | _ => loop
    loop

partial def interpolatedStr (p : LParse Syntax) : LParse InterpolatedStr :=
  node interpolatedStrKind <| atomic do
    let start ← getInputPos
    let leading : Substring :=
      {str := ← getInput, startPos := (← getIgnoredBefore).stopPos, stopPos := start}
    skipChar '"'
    let rec loop (head : String.Pos) (leading : Substring) (acc : Array Syntax) := do
      match (← next1) with
      | '\\' => skipEscapeSeq; loop head leading acc
      | '"' =>
        let input ← getInput
        let tail ← getInputPos
        let trailing ← consumeIgnored
        return acc.push <| mkNode interpolatedStrLitKind
          #[.atom (.original leading head trailing tail) (input.extract head tail)]
      | '{' =>
        let input ← getInput
        let tail ← getInputPos
        let trailing : Substring :=
          {str := input, startPos := tail, stopPos := tail}
        let acc := acc.push <| mkNode interpolatedStrLitKind
          #[.atom (.original leading head trailing tail) (input.extract head tail)]
        let acc := acc.push <| ← p
        let head ← getInputPos
        skipChar '}'
        loop head trailing acc
      | _ => loop head leading acc
    loop start leading #[]

def numLit : LParse NumLit :=
  node numLitKind <| Array.singleton <$> atomOf do
    let c ← digit
    if c = '0' then
      let b ← peek
      match b with
      | 'b' | 'B' => skip; skipMany1 bit
      | 'o' | 'O' => skip; skipMany1 octDigit
      | 'x' | 'X' => skip; skipMany1 hexDigit
      | _ => skipMany digit
    else
      skipMany digit

def scientificLit : LParse ScientificLit :=
  node scientificLitKind <| Array.singleton <$> atomOf do
    skipMany1 digit
    let expected := ["'.'", "'e'", "'E'"]
    let c ← next1 expected
    if c == '.' then
      skipMany digit
    else if c == 'e' || c == 'E' then
      skipIfSatisfy (fun c => c == '-' || c == '+') ["exponent"]
      skipMany1 digit
    else
      throwUnexpected s!"unexpected '{c}'" expected

def nameLit : LParse NameLit :=
  node nameLitKind <| Array.singleton <$> atomOf do
    skipChar '`'; discard name

@[inline] def optional (p : LParse (Array Syntax)) : LParse Syntax :=
  attemptD mkNullNode <| @mkNullNode <$> p

@[inline] def many (p : LParse Syntax) : LParse Syntax :=
  @mkNullNode <$> collectMany p

@[inline] def many1 (p : LParse Syntax) : LParse Syntax :=
  @mkNullNode <$> collectMany1 p

def many1Unbox (p : LParse Syntax) : LParse Syntax :=
  collectMany1 p <&> fun xs =>
    if _ : xs.size = 1 then xs[0]'(by simp [*]) else mkNullNode xs

partial def sepByTrailing (args : Array Syntax)
(p : LParse Syntax) (sep : LParse Syntax) : LParse Syntax := do
  if let some a ← attempt? p then
    let args := args.push a
    if let some s ← attempt? sep then
      sepByTrailing (args.push s) p sep
    else
      return mkNullNode args
  else
    return mkNullNode args

partial def sepBy1NoTrailing (args : Array Syntax)
(p : LParse Syntax) (sep : LParse Syntax) : LParse Syntax := do
  let args := args.push (← p)
  if let some s ← attempt? sep then
    sepBy1NoTrailing (args.push s) p sep
  else
    return mkNullNode args

def sepBy (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax := do
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
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax := do
  if allowTrailingSep then
    let a ← p
    if let some s ← attempt? psep then
      sepByTrailing #[a, s] p psep
    else
      return mkNullNode #[a]
  else
    sepBy1NoTrailing #[] p psep

@[inline] def pushNone : LParse Syntax :=
  pure mkNullNode

def sepByIndent (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax :=
  withPosition <| sepBy (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

def sepBy1Indent (p : LParse Syntax)
(sep : String) (psep : LParse Syntax := symbol sep) (allowTrailingSep := false) : LParse Syntax :=
  withPosition <| sepBy1 (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

@[inline] partial def trailingLoop (head : Syntax)
(trailing : Array (LParse (SyntaxNodeKind × Array Syntax))) (h : trailing.size > 0) : LParse Syntax :=
  step head
where
  step head := do
    let iniPos ← getInputPos
    checkpoint fun restore => do
    match (← observing <| longestMatch trailing h Parser.Error.merge) with
    | .ok (kind, args) =>
      let node := (.node .none kind <| #[head] ++ args)
      -- break the loop if a successful trailing parser does not consume anything
      if iniPos = (← getInputPos) then return node else step node
    | .error e =>
      if iniPos < (← getInputPos) then throw e else restore; return head

/-- Parse a category with the given `leading` and `trailing` parsers. -/
def category (name : Name) (leading : Array (LParse Syntax))
(trailing : Array (LParse (SyntaxNodeKind × Array Syntax))) : LParse (TSyntax name) := do
  setLhsPrec Parser.maxPrec
  if h : leading.size > 0 then
    let head ← longestMatch leading h Parser.Error.merge
    if h : trailing.size > 0 then
      (⟨·⟩) <$> trailingLoop head trailing h
    else
      return ⟨head⟩
  else
    throwUnexpected s!"attempted to parse category '{name}' with no leading parsers"

/-- Parse the category `name` stored within the `LParse` context. -/
def categoryRef (name : Name) (rbp : Nat := 0) : LParse (TSyntax name) := do
  if let some op := (← read).cats.find? name then
    (⟨·⟩) <$> withPrec rbp op.get
  else
    throwUnexpected s!"attempted to parse unknown category '{name}'"

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
