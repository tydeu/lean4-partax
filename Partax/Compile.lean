/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Parser.Extension
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Lean.Meta.Eval
import Partax.LParse
import Partax.Trace

open Lean

namespace Partax

--------------------------------------------------------------------------------
/-! ## Helpers Utilities                                                      -/
--------------------------------------------------------------------------------

local instance : Coe Name Ident where
  coe := mkIdent

def stripPrefix (p n : Name) : Name :=
  n.replacePrefix p .anonymous

@[inline] unsafe def unsafeEvalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr :=
  env.evalConst ParserDescr opts name

@[implemented_by unsafeEvalParserDescr] opaque evalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr

@[implemented_by Lean.Meta.evalExpr]
opaque evalExpr (α) (type : Expr) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

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

def undefinedGlobalName [Monad m] [MonadResolveName m] [MonadEnv m] (name : Name) : m Bool :=
  inline <| resolveGlobalName name <&> (·.filter (·.2.isEmpty) |>.isEmpty)

--------------------------------------------------------------------------------
/-! ## Compile Monad                                                          -/
--------------------------------------------------------------------------------

section
open Elab.Command (CommandElabM)

structure CompileState where
  /-- Categories used in compiling the current parser or category. -/
  cats : NameSet := {}
  /-- Associates each category with its used categories. -/
  catMap : NameMap NameSet := {}
  /-- Array of compiled parser definitions. -/
  defs : Array Command := #[]
  /-- Set of definitions already compiled. -/
  compiled : NameSet := {}

abbrev CompileT m := StateT CompileState m

def CompileT.run [Functor m] (x : CompileT m α) : m (Array Command) :=
  StateT.run x {} <&> (·.2.defs)

@[inline] def pushCmd [Monad m] (cmd : Command) : CompileT m PUnit :=
  modify fun s => {s with defs := s.defs.push cmd}

@[inline] def addCategory [Monad m] (name : Name) : CompileT m PUnit :=
  modify fun s => {s with cats := s.cats.insert name}

/-- Ensure `name` is marked and return whether it already was. -/
@[inline] def checkOrMarkVisited [Monad m] (name : Name) : CompileT m Bool :=
  modifyGet fun s =>
    if s.compiled.contains name then (true, s)
    else (false, {s with compiled := s.compiled.insert name})

abbrev CompileM := CompileT CommandElabM

def withStepTrace (name : Name) (k : CompileM α) (collapsed := false) : CompileM α := do
  inline <| withTraceNode `Partax.compile.step (fun _ => return mkConst name) k collapsed

@[inline] def pushDef (name : Name) (value : Term) : CompileM PUnit := do
  pushCmd <| ← `(def $name := $value)

@[inline] def pushAliasDef (name : Name) (alias : Name) : CompileM PUnit := do
  pushCmd <| ← `(@[inline] def $name := $(mkCIdentFrom (← getRef) alias))

def pushCategoriesDef (ns : Name) (cats : NameSet)  : CompileM PUnit := do
  let entries ← cats.foldM (init := #[]) fun a n =>
    return a.push <| ← ``(($(quote n), $(mkIdent n)))
  let catMap ← ``((RBMap.ofList [$entries,*] : CategoryMap))
  pushDef (ns.str "categories") catMap

def pushCategoriesDefs : CompileM PUnit := do
  let s ← get; s.cats.forM fun cat => do
    if let some cats := s.catMap.find? cat then
      pushCategoriesDef cat cats

end

--------------------------------------------------------------------------------
/-! ## Compile Configuration                                                  -/
--------------------------------------------------------------------------------

/-
Dummy helpers just for WIP testing purposes
-/
namespace LParse

def decimal : LParse Syntax := atomOf do
  skipMany digit

@[inline] def dummy : LParse Syntax := do
  error "dummy parser"

end LParse

def syntaxAliases :=
  ({} : NameMap Name)
  |>.insert `decimal ``LParse.decimal

def parserAliases :=
  ({} : NameMap Name)
  -- Primitives
  |>.insert ``Parser.rawCh ``LParse.rawCh
  |>.insert ``Parser.ident ``LParse.ident
  |>.insert ``Parser.rawIdent ``LParse.ident
  |>.insert ``Parser.symbol ``LParse.symbol
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

abbrev AppHandler :=
  (Expr → CompileM Term) → Array Expr → CompileM Term

open Parser in
def parserAppHandlers :=
  ({} : NameMap AppHandler)
  |>.insert ``ppIndent compileArg0
  |>.insert ``ppDedent compileArg0
  |>.insert ``ppRealFill compileArg0
  |>.insert ``ppRealGroup compileArg0
  |>.insert ``ppGroup compileArg0
  |>.insert ``ppDedentIfGrouped compileArg0
  |>.insert ``patternIgnore compileArg0
  |>.insert ``incQuotDepth compileArg0
  |>.insert ``suppressInsideQuot compileArg0
  |>.insert ``withCache compileArg1
  |>.insert ``withResetCache compileArg0
  |>.insert ``withAntiquot compileArg1
  |>.insert ``withAntiquotSpliceAndSuffix compileArg1
  |>.insert ``withOpen compileArg0
  |>.insert ``withOpenDecl compileArg0
  |>.insert ``withForbidden compileArg1
  |>.insert ``withoutForbidden compileArg0
  |>.insert ``Parser.andthen compileParserAndThen
  |>.insert ``HAndThen.hAndThen compileAndThen
  |>.insert ``Parser.orelse compileParserOrElse
  |>.insert ``HOrElse.hOrElse compileOrElse
  |>.insert ``parserOfStack mkDummy
  |>.insert ``checkStackTop mkDummy
where
  mkDummy _ _ :=
    return mkCIdent ``LParse.dummy
  compileArg0 compileExpr args :=
    compileExpr args[0]!
  compileArg1 compileExpr args :=
    compileExpr args[1]!
  compileAndThen compileExpr args := do
    let p1 ← compileExpr args[4]!
    let p2 ← compileExpr args[5]!.bindingBody!
    return (← `($p1 >> $p2))
  compileParserAndThen compileExpr args := do
    let p1 ← compileExpr args[0]!
    let p2 ← compileExpr args[1]!
    return (← `($p1 >> $p2))
  compileOrElse compileExpr args := do
    let p1 ← compileExpr args[4]!
    let p2 ← compileExpr args[5]!.bindingBody!
    return (← `($p1 <|> $p2))
  compileParserOrElse compileExpr args := do
    let p1 ← compileExpr args[0]!
    let p2 ← compileExpr args[1]!
    return (← `($p1 <|> $p2))

--------------------------------------------------------------------------------
/-! ## Compile Functions                                                      -/
--------------------------------------------------------------------------------

section
open Meta Elab Term Command Syntax Parser

partial def compileParserExpr (x : Expr) : CompileM Term :=
  compileExpr x
where
  compileExpr x := do
    match x with
    | .const name _ => do
      if let some alias := parserAliases.find? name then
        return mkCIdentFrom (← getRef) alias
      let pName := stripPrefix `Lean.Parser name
      let some info := (← getEnv).find? name
        | return mkIdentFrom (← getRef) name -- potential local constant
      let some numArgs ← checkParserType info
        | return mkIdentFrom (← getRef) name
      withTraceNode `Partax.compile.step (fun _ => return mkConst name) do
      if (← checkOrMarkVisited pName) then
        return mkIdentFrom (← getRef) pName
      if numArgs > 0 then
        throwError "cannot compile parameterized parser {name}"
      let some p := info.value?
        | throwError "cannot compile opaque definition '{name}'"
      if p.isAppOf ``Parser.mk then
        throwError "cannot compile primitive parser '{name}'"
      pushDef pName <| ← compileExpr p
      return mkIdentFrom (← getRef) pName
    | .app .. => do
      let fn := x.getAppFn
      let args := x.getAppArgs
      let .const fname _ := fn
        | return mkApp (← compileExpr fn) (← args.mapM compileExpr)
      if fname = ``OfNat.ofNat then
        return quote args[1]!.natLit?.get!
      else if (``Name).isPrefixOf fname then
        liftTermElabM <| liftMetaM do
          let name ← evalExpr Name (mkConst ``Name)  x
          return quote name
      else if fname = ``ite then
        -- Note: Assumes the condition is a constant
        let b ← liftTermElabM <| liftMetaM do
          evalExpr Bool (mkConst ``Bool) <| mkAppN (mkConst ``decide) #[args[1]!, args[2]!]
        if b then compileExpr args[3]! else compileExpr args[4]!
      else if fname = ``categoryParser then
        let catName ← liftTermElabM <| liftMetaM do
          evalExpr Name (mkConst ``Name) args[0]!
        if let some alias := syntaxAliases.find? catName then
          return mkCIdentFrom (← getRef) alias
        else
          addCategory catName
          let rbp ← compileExpr args[1]!
          ``(LParse.categoryRef $(quote catName) $rbp)
      else if let some handler := parserAppHandlers.find? fname then
        handler compileExpr args
      else if let some alias := parserAliases.find? fname then
        let args ← args.mapM compileExpr
        return mkApp (mkCIdentFrom (← getRef) alias) args
      else
        let some info := (← getEnv).find? fname
          | throwError "unknown constant '{fname}'"
        if let some numArgs ← checkParserType info then
          withStepTrace fname do
          if numArgs = args.size then
            let some pLam := info.value?
              | throwError "cannot compile opaque definition '{fname}'"
            let value := pLam.beta args
            if value.isAppOf ``Parser.mk || value.isAppOf ``Parser.withFn then
              throwError "cannot compile parameterized primitive parser '{fname}'"
            compileExpr value
          else
            throwError "cannot compile partial application of parameterized parser '{fname}'"
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
  @[inline] checkParserType info :=
    liftTermElabM <| liftMetaM <| forallTelescope info.type fun as r =>
      match r with
      | .const ``Parser _  | .const ``TrailingParser _  =>
        return some as.size
      | .const ``ParserFn _ =>
        throwError "cannot compile parser function '{info.name}'"
      | _ =>
        return none

def compileParserDescrToExpr (descr : ParserDescr) : CompileM Expr :=
  compileDescr descr
where
  compileAlias name args := do
    if let some name := syntaxAliases.find? name then
      return mkAppN (mkConst name) args
    else if let some name ← getParserAlias? name then
      return mkAppN (mkConst name) args
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
    let declName := stripPrefix `Lean.Parser kind
    unless (← checkOrMarkVisited declName) do
      withStepTrace kind do
      let x := mkAppN (mkConst ``Parser.node) #[toExpr kind, ← compileDescr p]
      let p ← compileParserExpr x
      pushDef declName p
    return mkConst declName
  | .sepBy p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]
  | .sepBy1 p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy1)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]

@[inline] def compileParserDescr (descr : ParserDescr) : CompileM Term :=
  compileParserDescrToExpr descr >>= compileParserExpr

def compileParserInfo (info : ConstantInfo) : CompileM (Bool × Term) := do
  let env ← getEnv
  have : MonadLift (Except String) CommandElabM :=
    ⟨fun | .ok a => pure a | .error e => throwError e⟩
  match info.type with
  | .const ``Parser .. =>
    let some x := info.value?
      | throwError "cannot compile opaque definition '{info.name}'"
    return (false, ← compileParserExpr x)
  | .const ``TrailingParser .. =>
    let some x := info.value?
      | throwError "cannot compile opaque definition '{info.name}'"
    return (true, ← compileParserExpr x)
  | .const ``ParserDescr .. =>
    let d ← evalParserDescr info.name env (← getOptions)
    return (false, ← compileParserDescr d)
  | .const ``TrailingParserDescr .. =>
    let d ← evalParserDescr info.name env (← getOptions)
    return (true, ← compileParserDescr d)
  | _ =>
    throwError "expected Parser or ParserDescr at '{info.name}'"

def compileParserConst (name : Name) : CompileM (Bool × Term) := do
  withStepTrace name do
  let some info := (← getEnv).find? name
    | throwError "unknown constant '{name}'"
  inline (compileParserInfo info)

partial def compileParserCategory (catName : Name) : CompileM PUnit := do
  withStepTrace (``Parser.Category ++ catName) (collapsed := true) do
  if (← checkOrMarkVisited catName) then
    return
  unless (← undefinedGlobalName catName) do
    return -- Use an existing definition if one exists
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let some cat := cats.find? catName
    | throwError "cannot compile unknown category `{catName}`"
  let ref ← getRef
  let mut leadingPs := #[]
  let mut trailingPs := #[]
  let prevCats ← modifyGet fun s => (s.cats, {s with cats := {}})
  for (k, _) in cat.kinds do
    let pName := stripPrefix `Lean.Parser k
    let pId := mkIdentFrom ref pName
    if (← checkOrMarkVisited pName) then
      leadingPs := leadingPs.push pId
      continue
    let name ← resolveGlobalConstNoOverload (mkIdentFrom ref k)
    if let some alias := syntaxAliases.find? name then
      leadingPs := leadingPs.push pId
      pushAliasDef pName alias
    else
      let (trailing, p) ← compileParserConst name
      if trailing then
        trailingPs := trailingPs.push pId
      else
        leadingPs := leadingPs.push pId
      pushDef pName p
  let value ← ``(
    LParse.category $(quote catName)
      #[$[($leadingPs : LParse Syntax)],*]
      #[$[($trailingPs : LParse Syntax)],*]
  )
  pushDef catName value
  (← get).cats.forM compileParserCategory
  modify fun s => {s with
    catMap := s.catMap.insert catName s.cats
    cats := s.cats.union <| prevCats.insert catName
  }

def compileParserInfoTopLevel (info : ConstantInfo) : CompileM Unit := do
  let (_, p) ← compileParserInfo info
  let pName := stripPrefix `Lean.Parser info.name
  unless (← checkOrMarkVisited pName) do
    pushDef pName p
  (← get).cats.forM compileParserCategory
  pushCategoriesDef .anonymous (← get).cats
  pushCategoriesDefs

end

--------------------------------------------------------------------------------
/-! ## Compile Commands                                                      -/
--------------------------------------------------------------------------------

section
open Elab Command Term PrettyPrinter

syntax dry := "(" noWs &"dry" noWs ")"

def traceDefs (defs : Array Command) : CommandElabM MessageData :=
  defs.foldlM (init := "") fun str cmd =>
    return str ++ s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"

scoped syntax "compile_parser_category " (dry)? ident : command
elab_rules : command | `(compile_parser_category $[$dry?]? $cat:ident) => do
  let catName := cat.getId
  let catDef := Lean.mkConst (``Parser.Category ++ catName)
  discard <| liftTermElabM <| addTermInfo cat catDef
  let defs ← compileParserCategory catName *> pushCategoriesDefs |>.run
  let cmd : Command := ⟨mkNullNode defs⟩
  trace[Partax.compile.result] ← traceDefs defs
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

scoped syntax "compile_parser " (dry)? ident (" as " ident)? : command
elab_rules : command | `(compile_parser $[$dry?]? $id $[as $root?]?) => do
  let name ← resolveGlobalConstNoOverload id
  let some info := (← getEnv).find? name
    | throwErrorAt id s!"unknown constant '{name}'"
  discard <| liftTermElabM <| addTermInfo id (mkConst name)
  let defs ← compileParserInfoTopLevel info |>.run
  let cmd : Command := ⟨mkNullNode defs⟩
  trace[Partax.compile.result] ← traceDefs defs
  let ns : Name := root?.getD id |>.getId.str "lParse"
  let root := root?.getD ns
  let pName := stripPrefix `Lean.Parser name
  let cmd ← `(namespace $ns $cmd end $ns abbrev $root := $(ns ++ pName))
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

end
