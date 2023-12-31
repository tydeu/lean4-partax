/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser.Extension
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Lean.Elab.Eval
import Partax.LParse
import Partax.Trace

open Lean

namespace Partax

--------------------------------------------------------------------------------
/-! ## Helper Utilities                                                      -/
--------------------------------------------------------------------------------

local instance : Coe Name Ident where
  coe := mkIdent

@[inline] def stripPrefix (p n : Name) : Name :=
  n.replacePrefix p .anonymous

def stripPrefixIf (f : Name → Bool) : Name → Name
| .anonymous   => .anonymous
| n@(.str p s) => if f n then .anonymous else .str (stripPrefixIf f p) s
| n@(.num p s) => if f n then .anonymous else .num (stripPrefixIf f p) s

@[implemented_by Lean.Environment.evalConstCheck] opaque evalConstCheck
(α) (env : Environment) (opts : Options) (typeName constName : Name) : ExceptT String Id α

@[inline] unsafe def unsafeEvalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr :=
  env.evalConst ParserDescr opts name

@[implemented_by unsafeEvalParserDescr] opaque evalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr

@[implemented_by Lean.Meta.evalExpr]
opaque evalExpr (α) (type : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

@[implemented_by Lean.Elab.Term.evalTerm]
opaque evalTerm (α) (type : Expr) (value : Syntax) (safety := DefinitionSafety.safe) : Elab.TermElabM α

@[inline] def getParserAlias? (aliasName : Name) : BaseIO (Option Name) := do
  return (← Parser.parserAliases2infoRef.get).find? aliasName |>.map (·.declName)

/-
The `bracketedBinder` parser has a default argument. However, it appears
a constant alias in the environment, which causes problems for compilation.
We fix this by changing the alias to point to `bracketedBinderF`, which is the
no argument version of `bracketedBinder`.
-/
open Parser Term in initialize
  parserAliases2infoRef.modify fun m =>
    if let some info := m.find? `bracketedBinder then
      m.insert `bracketedBinder {info with declName := ``bracketedBinderF}
    else
      have : Inhabited _ := ⟨m⟩
      panic! "expected alias for bracketedBinder"

def resolveGlobalNameNoOverload? [Monad m] [MonadResolveName m] [MonadEnv m] (name : Name) : m (Option Name) := do
  let cs ← inline <| resolveGlobalName name
  match cs.filter (·.2.isEmpty) with
  | [(c, _)] => return some c
  | _ => return none

--------------------------------------------------------------------------------
/-! ## Compile Monad                                                          -/
--------------------------------------------------------------------------------

@[inline] def NameSet.ofList (kws : List Name) : NameSet :=
  kws.foldl (init := {}) fun s kw => s.insert kw

section
open Elab.Command (CommandElabM)

/-- Metadata for a compiled parser. -/
structure ParserData where
  /-- Keywords used in the parser(s). -/
  kws : NameSet := {}
  /-- Symbols used in the parser(s). -/
  syms : SymbolSet := {}
  /-- Categories used in the parser(s). -/
  cats : NameSet := {}

@[inline] def ParserData.union (a b : ParserData) : ParserData where
  kws := a.kws.union b.kws
  syms := a.syms.union b.syms
  cats := a.cats.union b.cats

@[inline] def ParserData.addCategory (cat : Name) (self : ParserData) : ParserData :=
  {self with cats := self.cats.insert cat}

structure CompileContext where
  rootName : Name := .anonymous

structure CompileState extends ParserData where
  /-- Array of compiled parser definitions. -/
  defs : Array Command := #[]
  /-- Name-to-name mapping of definitions already compiled. -/
  compileMap : NameMap Name := {}
  /-- Compilation metadata for each parser definition. -/
  dataMap : NameMap ParserData := {}

abbrev CompileT m := ReaderT CompileContext <| StateT CompileState m

@[inline] def CompileT.run [Functor m] (x : CompileT m α) : m (Array Command) :=
  (StateT.run (ReaderT.run x {}) {}) <&> (·.2.defs)

abbrev CompileM := CompileT CommandElabM

@[inline] def pushCmd (cmd : Command) : CompileM PUnit :=
  modify fun s => {s with defs := s.defs.push cmd}

@[inline] def addKeyword (kw : Name) : CompileM PUnit :=
  modify fun s => {s with kws := s.kws.insert kw}

@[inline] def addSymbol (sym : String) : CompileM PUnit :=
  modify fun s => {s with syms := s.syms.insert sym}

@[inline] def addCategory (name : Name) : CompileM PUnit :=
  modify fun s => {s with cats := s.cats.insert name}

@[inline] def addParserDataOf (p : Name) : CompileM PUnit := do
  let s ← get
  if let some data := s.dataMap.find? p then
    set {s with toParserData := s.toParserData.union data}
  else
    throwError s!"missing data for parser '{p}'"

def withStepTrace (name : Name) (k : CompileM α) (collapsed := false) : CompileM α := do
  inline <| withTraceNode `Partax.compile.step (fun _ => return mkConst name) k collapsed

@[inline] def collectParserDataFor (pName : Name) (act : CompileM α) : CompileM α := do
  let iniData ← modifyGet fun s =>
    (s.toParserData, {s with toParserData := {}})
  let a ← act
  modify fun s => {s with
    toParserData := iniData.union s.toParserData
    dataMap := s.dataMap.insert pName s.toParserData
  }
  return a

@[inline] def pushDef (name : Name) (value : Term) : CompileM PUnit := do
  pushCmd <| ← `(def $name := $value)

@[inline] def pushAliasDef (name : Name) (alias : Name) : CompileM PUnit := do
  pushCmd <| ← `(@[inline] def $name := $(mkCIdentFrom (← getRef) alias))

def pushKeywordsDef (ns : Name) (kws : NameSet)  : CompileM PUnit := do
  let kws := kws.fold (init := #[]) fun a n => a.push (quote n : Term)
  let kws ← ``(NameSet.ofList [$kws,*])
  pushDef (ns.str "keywords") kws

def pushSymbolsDef (ns : Name) (syms : SymbolSet)  : CompileM PUnit := do
  let syms := syms.fold (init := #[]) fun a s => a.push (quote s : Term)
  let trie ← ``(SymbolTrie.ofList [$syms,*])
  pushDef (ns.str "symbols") trie

def pushCategoriesDef (ns : Name) (cats : NameSet)  : CompileM PUnit := do
  let cats := cats.fold (init := #[]) fun a n => a.push (quote n : Term)
  let cats ← ``(NameSet.ofList [$cats,*])
  pushDef (ns.str "categories") cats

@[inline] def pushLParserDef (pName : Name) (data : ParserData) : CompileM PUnit := do
  pushKeywordsDef pName data.kws
  pushSymbolsDef pName data.syms
  pushCategoriesDef pName data.cats
  let maps ← data.cats.foldM (init := #[]) fun a n =>
    return a.push <| ← ``(($(quote n), $(mkIdent <| n.str "raw")))
  pushDef pName <| ← `(
    show LParser _ from {
      raw := $(mkIdent <| pName.str "raw")
      kws := $(mkIdent <| pName.str "keywords")
      syms := $(mkIdent <| pName.str "symbols")
      cats := ParserMap.ofList [$maps,*]
    }
  )

@[inline] def pushCategoriesDataDefs : CompileM PUnit := do
  let s ← get; s.cats.forM fun cat => do
    if (← resolveGlobalNameNoOverload? cat).isNone then
      let some pName := s.compileMap.find? cat
        | throwError "missing compile data for category '{cat}'"
      let some data := s.dataMap.find? cat
        | throwError "missing parser data for category '{cat}'"
      pushLParserDef pName data

end

instance [MonadReaderOf ρ n] [MonadLiftT m n] [Bind n] : MonadLiftT (ReaderT ρ m) (n) where
  monadLift x := readThe ρ >>= fun r => liftM <| x r

--------------------------------------------------------------------------------
/-! ## Compile Configuration                                                  -/
--------------------------------------------------------------------------------

section
open Elab.Command (liftTermElabM)

abbrev AppHandler (α) :=
  Name → Array Expr → (Expr → CompileM α) → CompileM α

structure CompileConfig where
  /-- Original parser to compiled parser name mapping. -/
  mapName (rootName : Name) (kind : Name) : Name
  /-- Constant-to-priority mappings for parsers in a category (default: 1000). -/
  parserPriorities : NameMap Nat := {}
  /-- Constant-to-constant overrides for constants referenced in `ParserDescr`. -/
  syntaxAliases : NameMap Name := {}
  /-- Constant-to-constant overrides for `Parser` constants. -/
  parserAliases : NameMap Name := {}
  /-- Constant-to-handler mappings for `Parser` function applications. -/
  parserAppHandlers : NameMap (AppHandler Term) := {}
  deriving Inhabited

/--
An app handler that compiles and returns the function's first argument.
Useful for unary functions translated to no-ops (e.g., `ppIndent`).
-/
def compileArg0 : AppHandler α := fun _ args compileExpr =>
  compileExpr args[0]!

/--
an app handler that compiles and returns the function's second argument.
Useful for metadata functions translated to no-ops (e.g., `withCache`).
-/
def compileArg1 : AppHandler α := fun _ args compileExpr =>
  compileExpr args[1]!

/-- Dummy parser for compiled parsers that are not properly supported. -/
@[inline] def LParse.unsupported (name : Name) : LParseM Syntax := do
  error s!"unsupported parser '{name}'"

/-- A parser app handler that produces a `LParse.unsupported`. -/
def compileUnsupported : AppHandler Term := fun name _ _ =>
  return Syntax.mkApp (mkCIdentFrom (← getRef) ``LParse.unsupported) #[quote name]

/-- A parser app handler that produces a `LParse.nop`. -/
def compileNop : AppHandler Term := fun _  _ _ =>
  return mkCIdentFrom (← getRef) ``LParse.nop

/-- Compile a `>>` `Expr` into a `>>` `Term`. -/
def compileHAndThen : AppHandler Term := fun _ args compileExpr => do
    let p1 ← compileExpr args[4]!
    let p2 ← compileExpr args[5]!.bindingBody!
    return (← `($p1 >> $p2))

/-- Compile `Lean.Parser.andthen` into `>>`. -/
def compileParserAndThen : AppHandler Term := fun _ args compileExpr => do
    let p1 ← compileExpr args[0]!
    let p2 ← compileExpr args[1]!
    return (← `($p1 >> $p2))

/-- Compile a `<|>` `Expr` into a `<|>` `Term`. -/
def compileHOrElse : AppHandler Term := fun _ args compileExpr => do
    let p1 ← compileExpr args[4]!
    let p2 ← compileExpr args[5]!.bindingBody!
    return (← `($p1 <|> $p2))

/-- Compile `Lean.Parser.orElse` into `<|>`. -/
def compileParserOrElse  : AppHandler Term := fun _ args compileExpr => do
    let p1 ← compileExpr args[0]!
    let p2 ← compileExpr args[1]!
    return (← `($p1 <|> $p2))

/-- Compile an `OfNat.ofNat` application into a nat literal. -/
def compileOfNat : AppHandler Term := fun _ args _ => do
  return quote args[1]!.natLit?.get!

/-- Compiles a static `if c then a else b` into `a` or `b` based on `c`. -/
def compileStaticIte : AppHandler Term := fun _ args compileExpr => do
  let b ← liftTermElabM do
    evalExpr Bool (mkConst ``Bool) <| mkAppN (mkConst ``decide) #[args[1]!, args[2]!]
  if b then compileExpr args[3]! else compileExpr args[4]!

/-- Compile a static symbol parser into either an `LParse.keyword` or an `LParse.symbol`. -/
def compileSymbol : AppHandler Term := fun _ args _ => do
  let sym ← liftTermElabM do
    evalExpr String (mkConst ``String) args[0]!
  let sym := sym.trim
  let kw := sym.toName
  if kw.isAnonymous then
    addSymbol sym
    ``(LParse.symbol $(quote sym))
  else
    addKeyword kw
    ``(LParse.keyword $(quote kw))

/-- Compile a static keyowrd `withForbidden` into a `LParse.withForbiddenKeyword`. -/
def compileWithForbidden  : AppHandler Term := fun _ args compileExpr => do
  let sym ← liftTermElabM do
    evalExpr String (mkConst ``String) args[0]!
  let kw := sym.trim.toName
  if kw.isAnonymous then
    throwError "compiling a non-keyword 'withForbidden' call is unsupported"
  else
    ``(LParse.withForbiddenKeyword $(quote kw) $(← compileExpr args[1]!))

/-- Compile a static `categoryParser` into a `LParse.categoryRef`, noting the category's use. -/
def compileCategoryParser : AppHandler Term := fun _ args compileExpr => do
  let catName ← liftTermElabM do
    evalExpr Name (mkConst ``Name) args[0]!
  addCategory catName
  let rbp ← compileExpr args[1]!
  ``(LParse.categoryRef $(quote catName) $rbp)

@[inline] def compileParserDef (cfg : CompileConfig)  (kind : Name) (compile : CompileM Term) : CompileM Name := do
  if let some pName := (← get).compileMap.find? kind then
    addParserDataOf pName
    return pName.str "raw"
  else
    let pName := cfg.mapName (← read).rootName kind
    let p ← collectParserDataFor pName do compile
    modify fun s => {s with compileMap := s.compileMap.insert kind pName}
    let pRawName := pName.str "raw"
    pushDef pRawName p
    return pRawName

def compileCategoryDef (cfg : CompileConfig)
(catName : Name) (leading trailing : Array (Name × Name)) : CompileM Unit := do
  let ref ← getRef
  let prioCmp a b : Bool :=
    cfg.parserPriorities.findD a.1 1000 < cfg.parserPriorities.findD b.1 1000
  let leading := leading.qsort prioCmp |>.map fun (_,n) => mkIdentFrom ref n
  let trailing := trailing.qsort prioCmp |>.map fun (_,n) => mkIdentFrom ref n
  let value ← ``(
    LParse.category $(quote catName)
      #[$[($leading : LParseM Syntax)],*]
      #[$[($trailing : LParseM (SyntaxNodeKind × Array Syntax))],*]
  )
  let pName := cfg.mapName (← read).rootName catName
  pushDef (pName.str "raw") value
  modify fun s => {s with compileMap := s.compileMap.insert catName pName}

/-- The standard compilation configuration for produce `LParse`-based definitions. -/
def CompileConfig.lParse : CompileConfig where
  mapName _rootName name :=
    stripPrefixIf (fun n => n == `Lean.Parser || n == `Lean) name
  parserPriorities :=
    ({} : NameMap Nat)
    -- low priority / apply last
    |>.insert ``Parser.Attr.simple 100 -- needed b/c no leading ident behavior
  syntaxAliases :=
    ({} : NameMap Name)
  parserAliases :=
    ({} : NameMap Name)
    -- Primitives
    |>.insert ``Parser.rawCh ``LParse.rawCh
    |>.insert ``Parser.ident ``LParse.ident
    |>.insert ``Parser.rawIdent ``LParse.ident
    |>.insert ``Parser.nonReservedSymbol ``LParse.nonReservedSymbol
    |>.insert ``Parser.unicodeSymbol ``LParse.unicodeSymbol
    |>.insert ``Parser.Command.commentBody ``LParse.commentBody
    |>.insert ``Parser.node ``LParse.node
    |>.insert ``Parser.leadingNode ``LParse.leadingNode
    |>.insert ``Parser.trailingNode ``LParse.trailingNode
    |>.insert ``Parser.pushNone ``LParse.pushNone
    |>.insert ``Parser.group ``LParse.group
    |>.insert ``Parser.hygieneInfo ``LParse.hygieneInfo
    |>.insert ``Parser.fieldIdx ``LParse.fieldIdx
    |>.insert ``Parser.strLit ``LParse.strLit
    |>.insert ``Parser.interpolatedStr ``LParse.interpolatedStr
    |>.insert ``Parser.charLit ``LParse.charLit
    |>.insert ``Parser.numLit ``LParse.numLit
    |>.insert ``Parser.scientificLit ``LParse.scientificLit
    |>.insert ``Parser.nameLit ``LParse.nameLit
    -- Combinators
    |>.insert ``Parser.atomic ``LParse.atomic
    |>.insert ``Parser.lookahead ``LParse.lookahead
    |>.insert ``Parser.notFollowedBy ``LParse.notFollowedBy
    |>.insert ``Parser.optional ``LParse.optional
    |>.insert ``Parser.many ``LParse.many
    |>.insert ``Parser.many1 ``LParse.many1
    |>.insert ``Parser.many1Unbox ``LParse.many1Unbox
    |>.insert ``Parser.sepBy ``LParse.sepBy
    |>.insert ``Parser.sepBy1 ``LParse.sepBy1
    |>.insert ``Parser.sepByIndent ``LParse.sepByIndent
    |>.insert ``Parser.sepBy1Indent ``LParse.sepBy1Indent
    |>.insert ``Parser.withoutForbidden ``LParse.withoutForbidden
    |>.insert ``Parser.checkPrec ``LParse.checkPrec
    |>.insert ``Parser.checkLhsPrec ``LParse.checkLhsPrec
    |>.insert ``Parser.checkWsBefore ``LParse.checkWsBefore
    |>.insert ``Parser.checkNoWsBefore ``LParse.checkNoWsBefore
    |>.insert ``Parser.checkLinebreakBefore ``LParse.checkLinebreakBefore
    |>.insert ``Parser.withPosition ``LParse.withPosition
    |>.insert ``Parser.withPositionAfterLinebreak ``LParse.withPositionAfterLinebreak
    |>.insert ``Parser.withoutPosition ``LParse.withoutPosition
    |>.insert ``Parser.errorAtSavedPos ``LParse.errorAtSavedPos
    |>.insert ``Parser.checkColGe ``LParse.checkColGe
    |>.insert ``Parser.checkColGt ``LParse.checkColGt
    |>.insert ``Parser.checkColEq ``LParse.checkColEq
    |>.insert ``Parser.checkLineEq ``LParse.checkLineEq
    |>.insert ``Parser.skip ``LParse.nop
    |>.insert ``Parser.ppSpace ``LParse.nop
    |>.insert ``Parser.ppHardSpace ``LParse.nop
    |>.insert ``Parser.ppLine ``LParse.nop
    |>.insert ``Parser.ppHardLineUnlessUngrouped ``LParse.nop
  parserAppHandlers :=
    ({} : NameMap (AppHandler Term))
    -- Utility expressions
    |>.insert ``ite compileStaticIte
    |>.insert ``OfNat.ofNat compileOfNat
    -- Parsers
    |>.insert ``Parser.symbol compileSymbol
    |>.insert ``Parser.categoryParser compileCategoryParser
    |>.insert ``Parser.andthen compileParserAndThen
    |>.insert ``Parser.withForbidden compileWithForbidden
    |>.insert ``HAndThen.hAndThen compileHAndThen
    |>.insert ``Parser.orelse compileParserOrElse
    |>.insert ``HOrElse.hOrElse compileHOrElse
    -- No-op Parsers
    |>.insert ``Parser.ppIndent compileArg0
    |>.insert ``Parser.ppDedent compileArg0
    |>.insert ``Parser.ppRealFill compileArg0
    |>.insert ``Parser.ppRealGroup compileArg0
    |>.insert ``Parser.ppGroup compileArg0
    |>.insert ``Parser.ppDedentIfGrouped compileArg0
    |>.insert ``Parser.patternIgnore compileArg0
    |>.insert ``Parser.incQuotDepth compileArg0
    |>.insert ``Parser.suppressInsideQuot compileArg0
    |>.insert ``Parser.withCache compileArg1
    |>.insert ``Parser.withResetCache compileArg0
    |>.insert ``Parser.withAntiquot compileArg1
    |>.insert ``Parser.withAntiquotSpliceAndSuffix compileArg1
    |>.insert ``Parser.withOpen compileArg0
    |>.insert ``Parser.withOpenDecl compileArg0
    |>.insert ``Parser.parserOfStack compileUnsupported
    |>.insert ``Parser.checkStackTop compileNop

end

--------------------------------------------------------------------------------
/-! ## Compile Functions                                                      -/
--------------------------------------------------------------------------------

section
open Meta Elab Term Command Syntax Parser

/-- Extract parser data from a precompiled definition. -/
def extractParserDataOf (kind const : Name) : CompileM PUnit := do
  let .ok kws := evalConstCheck NameSet (← getEnv) (← getOptions) ``NameSet (const.str "keywords")
    | throwError "parser '{const}' is missing a 'keywords : NameSet' definition"
  let .ok syms := evalConstCheck SymbolTrie (← getEnv) (← getOptions) ``SymbolTrie (const.str "symbols")
    | throwError "parser '{const}' is missing a 'symbols : SymbolTrie' definition"
  let .ok cats := evalConstCheck NameSet (← getEnv) (← getOptions) ``NameSet (const.str "categories")
    | throwError "parser '{const}' is missing a 'categories : NameSet definition"
  let data : ParserData := {kws, syms := syms.toSet, cats := cats}
  modify fun s => {s with
    toParserData := s.toParserData.union data
    compileMap := s.compileMap.insert kind const
    dataMap := s.dataMap.insert const data
  }

@[inline] def checkParserType (info : ConstantInfo) : MetaM (Option Nat) :=
  forallTelescope info.type fun as r =>
    match r with
    | .const ``Parser _  | .const ``TrailingParser _  =>
      return some as.size
    | .const ``ParserFn _ =>
      let const : Expr := mkConst info.name <| info.levelParams.map .param
      throwError "cannot compile parser function '{const}'"
    | _ =>
      return none

partial def compileParserExpr (cfg : CompileConfig) (x : Expr) : CompileM Term :=
  compileExpr x
where
  compileExpr x :=  do
    match x with
    | .const name _ => do
      if let some alias := cfg.parserAliases.find? name then
        return mkCIdentFrom (← getRef) alias
      let some info := (← getEnv).find? name
        | return mkIdentFrom (← getRef) name -- potential local constant
      let some numArgs ← liftTermElabM <| checkParserType info
        | return mkIdentFrom (← getRef) name
      withStepTrace name do
      if numArgs > 0 then
        throwError "cannot compile parameterized parser '{x}'"
      let some p := info.value?
        | throwError "cannot compile opaque definition '{x}'"
      if p.isAppOf ``Parser.mk then
        throwError "cannot compile primitive parser '{x}'"
      let pName ← compileParserDef cfg name do compileExpr p
      return mkIdentFrom (← getRef) pName
    | .app .. => do
      let fn := x.getAppFn
      let args := x.getAppArgs
      let .const fname _ := fn
        | return mkApp (← compileExpr fn) (← args.mapM compileExpr)
      if (``Name).isPrefixOf fname then liftTermElabM do
        return quote <| ← evalExpr Name (mkConst ``Name) x
      else if let some alias := cfg.parserAliases.find? fname then
        return mkApp (mkCIdentFrom (← getRef) alias) (← args.mapM compileExpr)
      else if let some handler := cfg.parserAppHandlers.find? fname then
        handler fname args compileExpr
      else
        let some info := (← getEnv).find? fname
          | return mkApp (← compileExpr fn) (← args.mapM compileExpr)
        if let some numArgs ← liftTermElabM <| checkParserType info then
          withStepTrace info.name do
          if numArgs = args.size then
            let some pLam := info.value?
              | throwError "cannot compile opaque definition '{fn}'"
            let value := pLam.beta args
            if value.isAppOf ``Parser.mk || value.isAppOf ``Parser.withFn then
              throwError "cannot compile parameterized primitive parser '{fn}'"
            compileExpr value
          else
            throwError "cannot compile partial application of parameterized parser '{fn}'"
        else
          return mkApp (← compileExpr fn) (← args.mapM compileExpr)
    | .letE _declName _type value body _nonDep =>
      compileExpr <| body.instantiate1 value
    | .lit v =>
      match v with
      | .natVal n => return quote n
      | .strVal s => return mkStrLit s
    | _ =>
      throwError "cannot compile{indentExpr x}"

def compileParserDescrToExpr (cfg : CompileConfig) (descr : ParserDescr) : CompileM Expr :=
  compileDescr descr
where
  compileAlias name args := do
    if let some alias := cfg.syntaxAliases.find? name then
      return mkAppN (mkConst alias) args
    else if let some alias ← getParserAlias? name then
      return mkAppN (mkConst alias) args
    else
      throwError s!"no syntax or parser defined for alias `{name}`"
  compileDescr
  | .const name => do
    compileAlias name #[]
  | .unary name p => do
    compileAlias name #[← compileDescr p]
  | .binary name p1 p2 => do
    compileAlias name #[← compileDescr p1, ← compileDescr p2]
  | .node kind prec p => do
    return mkAppN (mkConst ``leadingNode)
      #[toExpr kind, toExpr prec, ← compileDescr p]
  | .trailingNode kind prec lhsPrec p => do
    return mkAppN (mkConst ``trailingNode)
      #[toExpr kind, toExpr prec, toExpr lhsPrec, ← compileDescr p]
  | .symbol val => do
    return .app (mkConst ``symbol) (toExpr val)
  | .nonReservedSymbol val includeIdent => do
    return mkAppN (mkConst ``nonReservedSymbol) #[toExpr val, toExpr includeIdent]
  | .cat catName rbp => do
    return mkAppN (mkConst ``categoryParser) #[toExpr catName, toExpr rbp]
  | .parser name => do
    return mkConst name
  | .nodeWithAntiquot _name kind p => do -- No antiquote support
    withStepTrace kind do
    let pName ← compileParserDef cfg kind do
      let x := mkAppN (mkConst ``Parser.node) #[toExpr kind, ← compileDescr p]
      compileParserExpr cfg x
    return mkConst pName
  | .sepBy p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]
  | .sepBy1 p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy1)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]

@[inline] def compileParserDescr (cfg : CompileConfig) (descr : ParserDescr) : CompileM Term :=
  compileParserDescrToExpr cfg descr >>= compileParserExpr cfg

def compileParserInfoToExpr (cfg : CompileConfig) (info : ConstantInfo) : CompileM Expr := do
  match info.type with
  | .const ``Parser _ | .const ``TrailingParser _ =>
    match info.value? with
    | some x => return x
    | none => throwError "cannot compile opaque definition '{info.name}'"
  | .const ``ParserDescr _ | .const ``TrailingParserDescr _ =>
    match evalParserDescr info.name (← getEnv) (← getOptions) with
    | .ok d => compileParserDescrToExpr cfg d
    | .error e => throwError e
  | _ =>
    throwError "expected Parser or ParserDescr at '{info.name}'"

@[inline] def compileParserInfo (cfg : CompileConfig) (info : ConstantInfo) : CompileM Term := do
  compileParserInfoToExpr cfg info >>= compileParserExpr cfg

def compileParserCategoryCore (cfg : CompileConfig) (catName : Name) : CompileM PUnit := do
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let some cat := cats.find? catName
    | throwError "cannot compile unknown category `{catName}`"
  let mut leadingPs := #[]
  let mut trailingPs := #[]
  for (kind, _) in cat.kinds do
    let some info := (← getEnv).find? kind
      | throwError "no constant for parser kind '{kind}'"
    let p ← withStepTrace kind (collapsed := true) do
      compileParserDef cfg kind do compileParserInfo cfg info
    match info.type with
    | .const ``TrailingParser _ | .const ``TrailingParserDescr _ =>
      trailingPs := trailingPs.push (kind, p)
    | _ =>
      leadingPs := leadingPs.push (kind, p)
  compileCategoryDef cfg catName leadingPs trailingPs

partial def compileParserCategory (cfg : CompileConfig) (catName : Name) : CompileM PUnit := do
  addCategory catName
  withStepTrace (``Parser.Category ++ catName) (collapsed := true) do
  if let some pName := (← get).compileMap.find? catName then
    addParserDataOf pName
    return
  if let some catConst ← resolveGlobalNameNoOverload? catName then
    -- Use an existing definition if one exists
    extractParserDataOf catName catConst
    return
  collectParserDataFor catName do compileParserCategoryCore cfg catName
  (← get).cats.erase catName |>.forM (compileParserCategory cfg ·)
  modify fun s => {s with dataMap := s.dataMap.insert catName s.toParserData}

def compileParserCategoryTopLevel (cfg : CompileConfig) (catName : Name) : CompileM Unit := do
  withReader ({· with rootName := catName}) do
  compileParserCategory cfg catName
  pushCategoriesDataDefs

def compileParserInfoTopLevel (cfg : CompileConfig) (rootName : Name) (info : ConstantInfo) : CompileM Unit := do
  withReader ({· with rootName := rootName}) do
  withStepTrace info.name (collapsed := true) do
  let p ← compileParserInfo cfg info
  let pName ← do
    match (← get).compileMap.find? info.name with
    | some name => pure name
    | none =>
      let pName := cfg.mapName (← read).rootName info.name
      let pRawName := pName.str "raw"
      pushDef pRawName p
      modify fun s => {s with
        dataMap := s.dataMap.insert pName s.toParserData
        compileMap := s.compileMap.insert info.name pName
      }
      pure pName
  (← get).cats.forM (compileParserCategory cfg ·)
  pushCategoriesDataDefs
  pushLParserDef pName (← get).toParserData
  unless rootName = pName do
    pushDef rootName pName

end

--------------------------------------------------------------------------------
/-! ## Compile Commands                                                      -/
--------------------------------------------------------------------------------

section
open Elab Command Term PrettyPrinter

def traceDefs (defs : Array Command) : CommandElabM Unit := do
  trace[Partax.compile.result] ← defs.foldlM (init := "") fun str cmd =>
    return str ++ s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"

initialize defaultCompileConfigExt : EnvExtension CompileConfig ←
  registerEnvExtension (pure CompileConfig.lParse)

def evalCompileConfig (cfg : Term) : TermElabM CompileConfig :=
  evalTerm CompileConfig (mkConst ``CompileConfig) cfg

def evalOptCompileConfig (cfg? : Option Term) : TermElabM CompileConfig :=
  match cfg? with
  | some cfg => evalCompileConfig cfg
  | none =>  return defaultCompileConfigExt.getState (← getEnv)

/--
Set the default compile configuration
used by compile commands (`compile_parser[_category]`) in this file.
The initial default is `CompileConfig.lParse`.
-/
scoped syntax "set_parser_compile_config " term : command
elab_rules : command | `(set_parser_compile_config $cfg) => do
  let cfg ← liftTermElabM <| evalCompileConfig cfg
  modifyEnv (defaultCompileConfigExt.setState · cfg)

syntax dry := "(" noWs &"dry" noWs ")"

/--
Compiles the specified Lean parser / syntax category (e.g., `term`, `attr`).
Details of the process can be configured using a term of type `CompileConfig`
provided via an optional `with` clause. For example:

```
compile_parser_category attr with myCompileConfig
```

By default, the command will use `CompileConfig.lParse`, which produces
`LParseM` monadic parser definitions for nested parsers, and an `LParser`
definition for the category and any nested categories.

**NOTE:** Compiling large categories (e.g., `term`) can take minutes.
-/
scoped syntax "compile_parser_category " (dry)? ident (" with " term)? : command
elab_rules : command | `(compile_parser_category $[$dry?]? $cat:ident $[with $cfg?]?) => do
  let catName := cat.getId
  let catDef := Lean.mkConst (``Parser.Category ++ catName)
  discard <| liftTermElabM <| addTermInfo cat catDef
  let cfg ← liftTermElabM <| evalOptCompileConfig cfg?
  let defs ← compileParserCategoryTopLevel cfg catName |>.run
  let cmd : Command := ⟨mkNullNode defs⟩; traceDefs defs
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

/--
Compiles the specified Lean parser or syntax (e.g., `Lean.Parser.Term.attributes`).
Details of the process can be configured using a term of type `CompileConfig`
provided via an optional `with` clause. You can also provide a new name for
the top-level result via an optional `=>` clause. For example:

```
compile_parser Lean.Parser.Term.attributes => attrs with myConfig
```

By default, the command will use `CompileConfig.lParse`, which produces
`LParseM` monadic parser definitions for nested parsers, and `LParser`
definitions for nested categories and the top-level parser.

**NOTE:** Compiling parsers that have deep nesting / utilize large categories
(e.g., `command`, `term`, `tactic`) can take minutes.
-/
scoped syntax "compile_parser " (dry)? ident (" => " ident)? (" with " term)? : command
elab_rules : command | `(compile_parser $[$dry?]? $id $[=> $root?]? $[with $cfg?]?) => do
  let name ← resolveGlobalConstNoOverload id
  let some info := (← getEnv).find? name
    | throwErrorAt id s!"unknown constant '{name}'"
  discard <| liftTermElabM <| addTermInfo id (mkConst name)
  let cfg ← liftTermElabM <| evalOptCompileConfig cfg?
  let pName :=
    match root? with
    | some root => root.getId
    | none => cfg.mapName .anonymous info.name
  let defs ← compileParserInfoTopLevel cfg pName info |>.run
  let cmd : Command := ⟨mkNullNode defs⟩; traceDefs defs
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

end
