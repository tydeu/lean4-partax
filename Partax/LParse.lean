/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Syntax
import Lean.Message
import Lean.Parser.Extension
import Partax.Basic

open Lean

namespace Partax

export Lean.Parser (InputContext mkInputContext)

instance : Coe String InputContext where
  coe s := mkInputContext s "<input>"

abbrev FieldIdx := TSyntax fieldIdxKind
abbrev InterpolatedStr := TSyntax interpolatedStrKind

--------------------------------------------------------------------------------
-- # LParseM Type for Parsing Syntax
--------------------------------------------------------------------------------

opaque OLParseM.nonemptyType (α : Type u) : NonemptyType.{0}
/-- An opaque forward-declared version of `LParseM` for wrapping category parsers. -/
def OLParseM (α : Type α) : Type := OLParseM.nonemptyType α |>.type
instance : Nonempty (OLParseM α) :=  OLParseM.nonemptyType α |>.property

abbrev SymbolTrie := Lean.Data.Trie String
@[inline] def SymbolTrie.empty : SymbolTrie := {}
@[inline] def SymbolTrie.ofList (syms : List String) : SymbolTrie :=
  syms.foldl (init := {}) fun t s => t.insert s s

abbrev SymbolSet := RBTree String compare
@[inline] def SymbolSet.empty : SymbolSet := {}
@[inline] partial def SymbolTrie.toSet (trie : SymbolTrie) : SymbolSet :=
  go trie |>.run {} |>.run.2
where
  go : SymbolTrie → StateM SymbolSet Unit
    | .leaf a? => do
      if let some a := a? then
        modify (·.insert a)
    | .node1 a? _ t' => do
      if let some a := a? then
        modify (·.insert a)
      go t'
    | .node a? _ ts => do
      if let some a := a? then
        modify (·.insert a)
      ts.forM fun t' => go t'


abbrev ParserMap := NameMap (OLParseM Syntax)
@[inline] def ParserMap.empty : ParserMap := {}
@[inline] def ParserMap.keySet (map : ParserMap) : NameSet :=
  map.fold (init := {}) fun s k _ => s.insert k

structure LParseData where
  kws : NameSet := {}
  syms : SymbolTrie := {}
  cats : ParserMap := {}

structure LParseContext extends InputContext, LParseData where
  prec : Nat := 0
  savedPos? : Option String.Pos := none
  forbiddenKw : Name := .anonymous

@[inline] def mkLParseContext (ictx : InputContext) (data : LParseData := {}) (rbp := 0) : LParseContext :=
  {toInputContext := ictx, prec := rbp, toLParseData := data}

instance : Coe InputContext LParseContext where
  coe ictx := mkLParseContext ictx

structure LParseState where
  lhsPrec : Nat := 0
  inputPos : String.Pos := 0
  ignoredBefore : Substring := "".toSubstring

abbrev LParseError := Lean.Parser.Error

/-- Parser monadic transformer for Lean-style parsing. -/
abbrev LParseT (m) := ReaderT LParseContext <| ExceptT LParseError <| StateT LParseState m

/-- Combinatorial, monadic parser for Lean-style parsing. -/
abbrev LParseM := ReaderT LParseContext <| EStateM LParseError LParseState

instance [Pure m] : MonadLift LParseM (LParseT m) where
  monadLift p := fun r s =>
    match p r s with
    | .ok a s => pure (.ok a, s)
    | .error e s => pure (.error e, s)

/-- A parse function equipped with `LParseData` metadata about it. -/
structure LParser (α) extends LParseData where
  raw : LParseM α

@[inline] protected def LParser.map (f : α → β) (p : LParser α) : LParser β :=
  {raw := f <$> p.raw, toLParseData := p.toLParseData}

instance : Functor LParser where map := LParser.map

@[inline] protected def LParser.toLParseM (p : LParser α) : LParseM α :=
  withReader ({· with toLParseData := p.toLParseData}) p.raw

instance : MonadLift LParser LParseM where
  monadLift := LParser.toLParseM

instance : Coe (LParser α) (LParseM α) where
  coe := LParser.toLParseM

namespace OLParseM
unsafe def unsafeMk : LParseM α → OLParseM α := unsafeCast
@[implemented_by unsafeMk] opaque mk : LParseM α → OLParseM α
instance : Coe (LParseM α) (OLParseM α)  := ⟨mk⟩
instance : Inhabited (OLParseM α) := ⟨mk default⟩
unsafe def unsafeGet : OLParseM α → LParseM α := unsafeCast
@[implemented_by unsafeGet] opaque get : OLParseM α → LParseM α
instance : Coe (OLParseM α) (LParseM α) := ⟨get⟩
end OLParseM

@[inline] def ParserMap.ofList (xs : List (Name × LParseM Syntax)) : ParserMap :=
  xs.foldl (init := {}) fun m (k, v) => m.insert k v

class MonadIgnoredBefore (m : Type → Type u) where
  getIgnoredBefore : m Substring
  setIgnoredBefore : Substring → m PUnit

export MonadIgnoredBefore (getIgnoredBefore setIgnoredBefore)

instance [MonadLift m n] [MonadIgnoredBefore m] : MonadIgnoredBefore n where
  getIgnoredBefore := liftM (m := m) getIgnoredBefore
  setIgnoredBefore i := liftM (m := m) <| setIgnoredBefore i

namespace LParse
variable [Monad m] [MonadInput m] [ThrowUnexpected m]

@[inline] def skipCommentBody : m Unit := do
  let input ← getInput
  let expected := ["'-/'"]
  let rec @[specialize] loop (pos) (nesting : Nat) := do
    let ⟨h⟩ ← ensureNotEOI input pos expected
    let pos' := input.next' pos h
    match input.get' pos h with
    | '-' =>
      let rec @[specialize] dashLoop pos := do
        let ⟨h⟩ ← ensureNotEOI input pos expected
        let pos' := input.next' pos h
        match input.get' pos h with
        | '-' =>
          dashLoop pos'
        | '/' =>
          if nesting = 0 then
            setInputPos pos'
          else
            loop pos' (nesting-1)
        | _ =>
          loop pos' nesting
      dashLoop pos'
    | '/' =>
      let ⟨h'⟩ ← ensureNotEOI input pos' expected
      if input.get' pos' h' = '-' then
        loop (input.next' pos' h') (nesting+1)
      else
        loop pos' nesting
    | _ =>
      loop pos' nesting
  loop (← getInputPos) 0
termination_by
  loop pos _ => input.utf8ByteSize - pos.byteIdx
  dashLoop pos => input.utf8ByteSize - pos.byteIdx

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
@[specialize] def fullInput [MonadIgnoredBefore m] (p : m α) : m α := do
  consumeIgnored *> p <* checkEOI

end LParse

instance : MonadInput LParseM where
  getInput := (·.input) <$> read
  getInputPos := (·.inputPos) <$> get
  setInputPos pos := modify ({· with inputPos := pos})

instance : MonadIgnoredBefore LParseM where
  getIgnoredBefore := (·.ignoredBefore) <$> get
  setIgnoredBefore i := modify ({· with ignoredBefore := i})

instance : MonadBacktrack LParseState LParseM where
  saveState := fun _ s => .ok s s
  restoreState s := fun _ _ => .ok () s

instance : ThrowUnexpected LParseM where
  throwUnexpected unexpected expected := throw {unexpected, expected}

@[inline] def LParseM.run (ctx : LParseContext) (s : LParseState) (p : LParseM α) : Except String (α × LParseState) :=
  match p ctx s with
  | .ok a s => .ok (a, s)
  | .error e s =>
    let pos := ctx.fileMap.toPosition s.inputPos
    let msg := mkErrorStringWithPos ctx.fileName pos (toString e)
    .error msg

@[inline] def LParseM.run'
(ictx : InputContext) (p : LParseM α)
(data : LParseData := {}) (rbp := 0) : Except String α :=
  (·.1) <$> LParseM.run (mkLParseContext ictx data rbp) {} do LParse.fullInput p

def LParser.run (ictx : InputContext) (s : LParseState) (p : LParser α) (rbp := 0) : Except String (α × LParseState) :=
  p.raw.run (mkLParseContext ictx p.toLParseData rbp) s

@[inline] def LParser.run' (ictx : InputContext) (p : LParser α) (rbp := 0) : Except String α :=
  p.raw.run' ictx p.toLParseData rbp

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

def LParseT.run [Monad m]
(ctx : LParseContext) (s : LParseState) (p : LParseT m α) : ExceptT String m (α × LParseState) := do
  match (← p ctx s) with
  | (.ok a, _) => pure (a, s)
  | (.error e, s) =>
    let pos := ctx.fileMap.toPosition s.inputPos
    let msg := mkErrorStringWithPos ctx.fileName pos (toString e)
    throw msg

@[inline] def LParseT.run' [Monad m]
(ictx : InputContext) (p : LParseT m α)
(data : LParseData := {}) (rbp := 0) : ExceptT String m α :=
  (·.1) <$> LParseT.run (mkLParseContext ictx data rbp) {} do LParse.fullInput p

namespace LParse

@[inline] def mergeOrElse (p1 : LParseM α) (p2 : Unit → LParseM α) : LParseM α := do
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

instance : MonadOrElse LParseM := ⟨mergeOrElse⟩

/-- A do-nothing parser for aliasing. -/
@[always_inline, inline] def nop : LParseM PUnit := pure ()

/- `LParseM` specializations for better type inference. -/
protected abbrev atomic (p : LParseM α) : LParseM α := atomic p
protected abbrev lookahead (p : LParseM α) : LParseM PUnit := lookahead p
protected abbrev notFollowedBy (p : LParseM α) (msg : String := "element") : LParseM PUnit :=
  notFollowedBy p msg

@[inline] def error (msg : String := "parse failure") : LParseM α := do
  throw {unexpected := msg}

@[noinline] def unexpectedPrecMessage : String :=
  "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def throwUnexpectedPrec : LParseM PUnit :=
  throwUnexpected unexpectedPrecMessage

@[inline] def withForbiddenKeyword (kw : Name) (p : LParseM α) : LParseM α := do
  withReader ({· with forbiddenKw := kw}) p

@[inline] def withoutForbidden (p : LParseM α) : LParseM α := do
  withReader ({· with forbiddenKw := .anonymous}) p

@[inline] def withPrec (prec : Nat) (p : LParseM α) : LParseM α := do
  withReader ({· with prec}) p

@[inline] def checkPrec (prec : Nat) : LParseM PUnit := do
  unless (← read).prec ≤ prec do throwUnexpectedPrec

@[inline] def checkLhsPrec (prec : Nat) : LParseM PUnit := do
  unless (← get).lhsPrec ≥ prec do throwUnexpectedPrec

@[inline] def setLhsPrec (prec : Nat) : LParseM PUnit := do
  modify ({· with lhsPrec := prec})

@[inline] def checkWsBefore (errorMsg : String := "space before") : LParseM PUnit := do
  if (← getIgnoredBefore).isEmpty then error errorMsg

@[inline] def checkNoWsBefore (errorMsg : String := "no space before") : LParseM PUnit := do
  unless (← getIgnoredBefore).isEmpty do error errorMsg

@[inline] def checkLinebreakBefore (errorMsg : String := "line break") : LParseM PUnit := do
  unless (← getIgnoredBefore).contains '\n' do error errorMsg

@[inline] def withSavedPos (savedPos? : Option String.Pos) (p : LParseM α) : LParseM α := do
  withReader ({· with savedPos?}) p

@[inline] def withPosition (p : LParseM α) : LParseM α := do
  withSavedPos (← getInputPos) p

@[inline] def withPositionAfterLinebreak (p : LParseM α) : LParseM α  := do
  if (← getIgnoredBefore).contains '\n' then withPosition p else p

@[inline] def withoutPosition (p : LParseM α) : LParseM α := do
  withSavedPos none p

@[inline, inherit_doc Parser.errorAtSavedPos]
def errorAtSavedPos (msg : String) (delta : Bool) : LParseM PUnit := do
  if let some pos := (← read).savedPos? then
    if delta then setInputPos <| (← getInput).next pos
    error msg

@[inline] def checkSavedPos (f : Position → Position → Bool) (errorMsg : String) : LParseM PUnit := do
  let ctx ← read
  if let some savedPos := ctx.savedPos? then
    let savedPos := ctx.fileMap.toPosition savedPos
    let inputPos := ctx.fileMap.toPosition (← getInputPos)
    unless f inputPos savedPos do error errorMsg

@[inline] def checkColGe (errorMsg : String := "checkColGe") : LParseM PUnit := do
  checkSavedPos (·.column ≥ ·.column) errorMsg

@[inline] def checkColGt (errorMsg : String := "checkColGt") : LParseM PUnit := do
  checkSavedPos (·.column > ·.column) errorMsg

@[inline] def checkColEq (errorMsg : String := "checkColEq") : LParseM PUnit := do
  checkSavedPos (·.column = ·.column) errorMsg

@[inline] def checkLineEq (errorMsg : String := "checkLineEq") : LParseM PUnit := do
  checkSavedPos (·.line = ·.line) errorMsg

--------------------------------------------------------------------------------
-- # Syntax-specific Parsers
--------------------------------------------------------------------------------

instance : Coe (LParseM PUnit) (LParseM (Array Syntax)) where
  coe x := Functor.mapConst #[] x

instance : Coe (LParseM Syntax) (LParseM (Array Syntax)) where
  coe x := Array.singleton <$> x

instance : CoeOut (LParseM (Array (TSyntax k))) (LParseM (Array Syntax)) where
  coe x := x

instance : CoeOut (LParseM (TSyntax k)) (LParseM Syntax) where
  coe x := x

/- Like Lean, assumes all leading whitespace has already been consumed. -/
def withSourceInfo (p : LParseM α) : LParseM (SourceInfo × α) := do
  let start ← getInputPos
  let leading : Substring :=
    {str := ← getInput, startPos := (← getIgnoredBefore).stopPos, stopPos := start}
  let a ← p
  let stop ← getInputPos
  let trailing ← consumeIgnored
  let info := .original leading start trailing stop
  return (info, a)

def extractSourceInfo (p : LParseM α) : LParseM SourceInfo := do
  let (info, _) ← inline <| withSourceInfo p
  return info

def identAtom : LParseM String := do
  if (← trySatisfy isIdBeginEscape) then
    let ident ← extract do
      skipToSatisfy isIdEndEscape ["end of identifier escape"]
    skip
    return ident
  else
    extract do
      skipSatisfy isIdFirst ["ident"]
      skipMany <| skipSatisfy isIdRest

partial def name : LParseM Name := do
  let rec identCont (n : Name) := do
    if let some s ← attempt? <| atomic <| skipChar '.' *> identAtom then
      identCont (.str n s)
    else
      return n
  let s ← identAtom
  identCont (.str .anonymous s)

def ident : LParseM Ident := do
  let (info, rawVal, val) ← atomic <| withSourceInfo <| withSubstring do
    let n ← name
    if (← read).kws.contains n then
      throwUnexpected s!"unexpected keyword '{n}'" ["ident"]
    else
      pure n
  return ⟨.ident info rawVal val []⟩

@[inline] def atomOf (p : LParseM PUnit) : LParseM Syntax := do
  let (info, val) ← atomic <| withSourceInfo <| extract p
  return .atom info val

@[inline] def atom (val : String) : LParseM Syntax := do
  let info ← atomic <| extractSourceInfo <| skipString val
  return .atom info val

def rawCh (c : Char) (trailingWs := false) : LParseM Syntax := do
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

@[inline] def keyword (kw : Name) : LParseM Syntax :=
  atomOf do
    let n ← name
    if n = kw then
      if kw = (← read).forbiddenKw then
        error "forbidden keyword"
     else
      throwUnexpected "unexpected ident '{n}'" [s!"'{kw}'"]

def symbol (sym : String) : LParseM Syntax := do
  let sym := sym.trim
  let info ← extractSourceInfo do
    let iniPos ← getInputPos
    let nextSym? := (← read).syms.matchPrefix (← getInput) iniPos
    let expected := [s!"'{sym}'"]
    if let some nextSym := nextSym? then
      if sym = nextSym then
        setInputPos (iniPos + nextSym)
      else
        throwUnexpected s!"unexpected symbol '{nextSym}'" expected
    else
      throwUnexpected s!"unexpected non-symbol syntax" expected
  return .atom info sym

@[inline] def nonReservedSymbol (sym : String) (_includeIdent := false) : LParseM Syntax :=
  atom sym.trim

def unicodeSymbol (sym asciiSym : String) : LParseM Syntax :=
  atomOf (skipString sym.trim <|> skipString asciiSym.trim)

@[inline] def node (kind : SyntaxNodeKind) (p : LParseM (Array Syntax)) : LParseM (TSyntax kind) := do
  let args ← try p catch e => throw {e with unexpected := s!"{kind}: {e.unexpected}"}
  return ⟨.node .none kind args⟩

@[inline] def leadingNode (kind : SyntaxNodeKind) (prec : Nat) (p : LParseM (Array Syntax)) : LParseM (TSyntax kind) := do
  checkPrec prec; let n ← node kind p; setLhsPrec prec; return n

@[inline] def trailingNode (kind : SyntaxNodeKind) (prec lhsPrec : Nat) (p : LParseM (Array Syntax)) : LParseM (SyntaxNodeKind × Array Syntax) := do
  checkPrec prec; checkLhsPrec lhsPrec; let args ← p; setLhsPrec prec; return (kind, args)

@[inline] def group (p : LParseM (Array Syntax)) : LParseM Syntax :=
  node groupKind p

def commentBody : LParseM Syntax :=
  atomOf skipCommentBody

def hygieneInfo : LParseM HygieneInfo :=
  node hygieneInfoKind do
    let pos ← getInputPos
    let str : Substring :=
      {str := ← getInput, startPos := pos, stopPos := pos}
    let info := SourceInfo.original str pos str pos
    return #[.ident info str .anonymous []]

def fieldIdx : LParseM FieldIdx :=
  node fieldIdxKind <| Array.singleton <$> atomOf do
    skipSatisfy fun c => '1' ≤ c ∧ c ≤ '9'
    skipMany digit

def skipEscapeSeq : LParseM PUnit := do
  match (← next1) with
  | 'x' => discard hexDigit; discard hexDigit
  | 'u' => discard hexDigit; discard hexDigit; discard hexDigit; discard hexDigit
  | _ => pure ()

def charLit : LParseM CharLit :=
  node charLitKind <| Array.singleton <$> atomOf do
    skipChar '\''
    if (← next1) = '\\' then skipEscapeSeq
    skipChar '\''

partial def strLit : LParseM StrLit :=
  node strLitKind <| Array.singleton <$> atomOf do
    skipChar '"'
    let rec loop := do
      match (← next1) with
      | '\\' => skipEscapeSeq; loop
      | '"' => return
      | _ => loop
    loop

partial def interpolatedStr (p : LParseM Syntax) : LParseM InterpolatedStr :=
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

def numLit : LParseM NumLit :=
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

def scientificLit : LParseM ScientificLit :=
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

def nameLit : LParseM NameLit :=
  node nameLitKind <| Array.singleton <$> atomOf do
    skipChar '`'; discard name

@[inline] def optional (p : LParseM (Array Syntax)) : LParseM Syntax :=
  attemptD mkNullNode <| @mkNullNode <$> p

@[inline] def many (p : LParseM Syntax) : LParseM Syntax :=
  @mkNullNode <$> collectMany p

@[inline] def many1 (p : LParseM Syntax) : LParseM Syntax :=
  @mkNullNode <$> collectMany1 p

def many1Unbox (p : LParseM Syntax) : LParseM Syntax :=
  collectMany1 p <&> fun xs =>
    if _ : xs.size = 1 then xs[0]'(by simp only [*]; decide) else mkNullNode xs

partial def sepByTrailing (args : Array Syntax)
(p : LParseM Syntax) (sep : LParseM Syntax) : LParseM Syntax := do
  if let some a ← attempt? p then
    let args := args.push a
    if let some s ← attempt? sep then
      sepByTrailing (args.push s) p sep
    else
      return mkNullNode args
  else
    return mkNullNode args

partial def sepBy1NoTrailing (args : Array Syntax)
(p : LParseM Syntax) (sep : LParseM Syntax) : LParseM Syntax := do
  let args := args.push (← p)
  if let some s ← attempt? sep then
    sepBy1NoTrailing (args.push s) p sep
  else
    return mkNullNode args

def sepBy (p : LParseM Syntax)
(sep : String) (psep : LParseM Syntax := symbol sep) (allowTrailingSep := false) : LParseM Syntax := do
  if allowTrailingSep then
    sepByTrailing #[] p psep
  else if let some a ← attempt? p then
    if let some s ← attempt? psep then
      sepBy1NoTrailing #[a, s] p psep
    else
      return mkNullNode #[a]
  else
    return mkNullNode

def sepBy1 (p : LParseM Syntax)
(sep : String) (psep : LParseM Syntax := symbol sep) (allowTrailingSep := false) : LParseM Syntax := do
  if allowTrailingSep then
    let a ← p
    if let some s ← attempt? psep then
      sepByTrailing #[a, s] p psep
    else
      return mkNullNode #[a]
  else
    sepBy1NoTrailing #[] p psep

@[inline] def pushNone : LParseM Syntax :=
  pure mkNullNode

def sepByIndent (p : LParseM Syntax)
(sep : String) (psep : LParseM Syntax := symbol sep) (allowTrailingSep := false) : LParseM Syntax :=
  withPosition <| sepBy (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

def sepBy1Indent (p : LParseM Syntax)
(sep : String) (psep : LParseM Syntax := symbol sep) (allowTrailingSep := false) : LParseM Syntax :=
  withPosition <| sepBy1 (checkColGe *> p) sep (psep <|> checkColEq *> checkLinebreakBefore *> pushNone) allowTrailingSep

@[inline] def trailingLoop (head : Syntax)
(trailing : Array (LParseM (SyntaxNodeKind × Array Syntax))) (h : trailing.size > 0) : LParseM Syntax := do
  let rec step input iniPos head :=
    if _ : input.atEnd iniPos then
      return head
    else
      checkpoint fun restore => do
      match (← observing <| longestMatch trailing h Parser.Error.merge) with
      | .ok (kind, args) =>
        let node := (.node .none kind <| #[head] ++ args)
        -- break the loop if a successful trailing parser does not consume anything
        let newPos ← getInputPos
        if iniPos < newPos then
          step input newPos node
        else
          return node
      | .error e =>
        if iniPos < (← getInputPos) then
          throw e
        else
          restore
          return head
  step (← getInput) (← getInputPos) head
termination_by
  step input pos _ => input.utf8ByteSize - pos.byteIdx

/-- Parse a category with the given `leading` and `trailing` parsers. -/
def category (name : Name) (leading : Array (LParseM Syntax))
(trailing : Array (LParseM (SyntaxNodeKind × Array Syntax))) : LParseM (TSyntax name) := do
  setLhsPrec Parser.maxPrec
  if h : leading.size > 0 then
    let head ← longestMatch leading h Parser.Error.merge
    if h : trailing.size > 0 then
      (⟨·⟩) <$> trailingLoop head trailing h
    else
      return ⟨head⟩
  else
    throwUnexpected s!"attempted to parse category '{name}' with no leading parsers"

/-- Parse the category `name` stored within the `LParseM` context. -/
def categoryRef (name : Name) (rbp : Nat := 0) : LParseM (TSyntax name) := do
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
  orElse : LParseM α → LParseM β → LParseM γ

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

instance [LParseOrElse α β γ] : HOrElse (LParseM α) (LParseM β) (LParseM γ) where
  hOrElse p1 p2 := LParseOrElse.orElse p1 (p2 ())

class LParseAndThen (α : Type) (β : Type) (γ : outParam Type) where
  andThen : LParseM α → LParseM β → LParseM γ

instance [LParseAndThen α β γ] : HAndThen (LParseM α) (LParseM β) (LParseM γ) where
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
