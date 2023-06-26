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

def stripUpperPrefix : Name → Name
| .anonymous => .anonymous
| .str p s => if s.get 0 |>.isUpper then .anonymous else .str (stripUpperPrefix p) s
| .num p n => .num (stripUpperPrefix p) n

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

--------------------------------------------------------------------------------
/-! ## Compile Monad                                                          -/
--------------------------------------------------------------------------------

section
open Elab.Command (CommandElabM)

structure CompileState where
  compiled : NameSet := .empty
  defs : Array Command := #[]

abbrev CompileT m := ReaderT Name <| StateT CompileState m
def CompileT.run [Functor m] (x : CompileT m α) : m (Array Command) :=
  StateT.run (ReaderT.run x .anonymous) {} <&> (·.2.defs)

abbrev CompileM := CompileT CommandElabM

def withStepTrace (name : Name) (k : CompileM α) (collapsed := false) : CompileM α := do
  inline <| withTraceNode `Partax.compile.step (fun _ => return mkConst name) k collapsed

/-- Ensure `name` is marked and return whether it already was. -/
@[inline] def checkOrMarkVisited [Monad m] (name : Name) : CompileT m Bool :=
  modifyGet fun s =>
    if s.compiled.contains name then (true, s)
    else (false, {s with compiled := s.compiled.insert name})

@[inline] def pushCmd [Monad m] (cmd : Command) : CompileT m PUnit :=
  modify fun s => {s with defs := s.defs.push cmd}

@[inline] def pushDef (name : Name) (value : Term) : CompileM PUnit := do
  pushCmd <| ← `(partial def $name := $value)

@[inline] def pushAliasDef (name : Name) (alias : Name) : CompileM PUnit := do
  pushCmd <| ← `(@[inline] partial def $name := $(mkCIdentFrom (← getRef) alias))

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
  fail "dummy parser"

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
  |>.insert ``Parser.fieldIdx ``LParse.fieldIdx
  |>.insert ``Parser.Term.hole ``LParse.hole
  |>.insert ``Parser.strLit ``LParse.strLit
  |>.insert ``Parser.charLit ``LParse.charLit
  |>.insert ``Parser.numLit ``LParse.numLit
  |>.insert ``Parser.scientificLit ``LParse.scientificLit
  |>.insert ``Parser.nameLit ``LParse.nameLit
  |>.insert ``Parser.symbol ``LParse.symbol
  |>.insert ``Parser.nonReservedSymbol ``LParse.nonReservedSymbol
  |>.insert ``Parser.unicodeSymbol ``LParse.unicodeSymbol
  |>.insert ``Parser.node ``LParse.node
  |>.insert ``Parser.leadingNode ``LParse.leadingNode
  |>.insert ``Parser.trailingNode ``LParse.trailingNode
  |>.insert ``Parser.pushNone ``LParse.pushNone
  -- Combinators
  |>.insert ``Parser.atomic ``atomic
  |>.insert ``Parser.lookahead ``lookahead
  |>.insert ``Parser.notFollowedBy ``notFollowedBy
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
  |>.insert ``Parser.ppSpace ``LParse.nop
  |>.insert ``Parser.ppLine ``LParse.nop
  |>.insert ``Parser.skip ``LParse.nop
  -- Placeholders
  |>.insert ``Parser.Command.commentBody ``LParse.dummy

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
  |>.insert ``interpolatedStr mkDummy
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

@[inline] def compileCatUse
(compileCat : Name → CompileM PUnit)
(catName : Name) (rbp : Term) : CompileM Term := do
  if let some alias := syntaxAliases.find? catName then
    return mkCIdentFrom (← getRef) alias
  else
    compileCat catName
    ``(LParse.withPrec $rbp $catName)

partial def compileParserExpr
(compileCat : Name → CompileM PUnit) (x : Expr) : CompileM Term :=
  compileExpr x
where
  compileExpr x := do
    match x with
    | .const name _ => do
      if let some alias := parserAliases.find? name then
        return mkCIdentFrom (← getRef) alias
      let pName := (← read) ++ stripUpperPrefix name
      let some info := (← getEnv).find? name
        | throwError s!"unknown constant '{name}'"
      let some numArgs ← checkParserType info
        | return mkCIdentFrom (← getRef) name
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
        let rbp ← compileExpr args[1]!
        let use ← compileCatUse compileCat catName rbp
        return use
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
              | throwError "cannot compile opaque definition '{info.name}'"
            let value := pLam.beta args
            if value.isAppOf ``Parser.mk || value.isAppOf ``Parser.withFn then
              throwError "cannot compile parameterized primitive parser '{fname}'"
            compileExpr value
          else
            throwError "cannot compile parameterized parser {fname}"
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

def compileParserDescrToExpr (descr : ParserDescr) : IO Expr :=
  compileDescr descr
where
  compileAlias name args := do
    if let some name := syntaxAliases.find? name then
      return mkAppN (mkConst name) args
    else if let some name ← getParserAlias? name then
      return mkAppN (mkConst name) args
    else
      throw <| IO.userError s!"no syntax or parser defined for alias `{name}`"
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
    return mkAppN (mkConst ``Parser.node) #[toExpr kind, ← compileDescr p]
  | .sepBy p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]
  | .sepBy1 p sep psep allowTrailingSep => do
    return mkAppN (mkConst ``sepBy1)
      #[← compileDescr p, toExpr sep, ← compileDescr psep, toExpr allowTrailingSep]

partial def compileParserDescr
(compileCat : Name → CompileM PUnit) (descr : ParserDescr) : CompileM Term :=
  compileDescr descr
where
  compileAlias name args := do
    if let some name := syntaxAliases.find? name then
      let args ← args.mapM compileDescr
      return mkApp (mkCIdentFrom (← getRef) name) args
    else if let some name ← getParserAlias? name then
      let args ← liftM <| args.mapM compileParserDescrToExpr
      compileParserExpr compileCat <| mkAppN (mkConst name) args
    else
      throwError s!"no syntax or parser defined for alias `{name}`"
  compileDescr
  | .const name => do
    compileAlias name #[]
  | .unary name p => do
    compileAlias name #[p]
  | .binary name p1 p2 => do
    compileAlias name #[p1, p2]
  | .node kind prec p => do
    let p ← compileDescr p
    ``(LParse.leadingNode $(quote kind) $(quote prec) $p)
  | .trailingNode kind prec lhsPrec p => do
    let p ← compileDescr p
    ``(LParse.trailingNode $(quote kind) $(quote prec) $(quote lhsPrec) $p)
  | .symbol val => do
    ``(LParse.symbol $(quote val))
  | .nonReservedSymbol val includeIdent => do
    ``(LParse.nonReservedSymbol $(quote val) $(quote includeIdent))
  | .cat catName rbp => do
    compileCatUse compileCat catName (quote rbp)
  | .parser name => do
    compileParserExpr compileCat (mkConst name)
  | .nodeWithAntiquot _name kind p => do -- No antiquote support
    let nName := (← read) ++ stripUpperPrefix kind
    if (← checkOrMarkVisited nName) then
      return mkIdentFrom (← getRef) nName
    let p ← compileDescr p
    let value ← ``(LParse.node $(quote kind) $p)
    pushDef nName value
    return mkIdentFrom (← getRef) nName
  | .sepBy p sep psep allowTrailingSep => do
    let p ← compileDescr p
    let psep ← compileDescr psep
    ``(LParse.sepBy $p $(quote sep) $psep $(quote allowTrailingSep))
  | .sepBy1 p sep psep allowTrailingSep => do
    let p ← compileDescr p
    let psep ← compileDescr psep
    ``(LParse.sepBy1 $p $(quote sep) $psep $(quote allowTrailingSep))

def compileParserInfo
(compileCat : Name → CompileM PUnit)
(info : ConstantInfo) : CompileM (Bool × Term) := do
  let env ← getEnv
  have : MonadLift (Except String) CommandElabM :=
    ⟨fun | .ok a => pure a | .error e => throwError e⟩
  match info.type with
  | .const ``Parser .. =>
    let some x := info.value?
      | throwError "cannot compile opaque definition '{info.name}'"
    return (false, ← compileParserExpr compileCat x)
  | .const ``TrailingParser .. =>
    let some x := info.value?
      | throwError "cannot compile opaque definition '{info.name}'"
    return (true, ← compileParserExpr compileCat x)
  | .const ``ParserDescr .. =>
    let d ← evalParserDescr info.name env (← getOptions)
    return (false, ← compileParserDescr compileCat d)
  | .const ``TrailingParserDescr .. =>
    let d ← evalParserDescr info.name env (← getOptions)
    return (true, ← compileParserDescr compileCat d)
  | _ =>
    throwError "expected Parser or ParserDescr at '{info.name}'"

def compileParserConst
(compileCat : Name → CompileM PUnit)
(name : Name) : CompileM (Bool × Term) := do
  withStepTrace name do
  let some info := (← getEnv).find? name
    | throwError "unknown constant '{name}'"
  inline (compileParserInfo compileCat info)

-- Requires `mutual partial` definitions of parsers
partial def compileParserCat
(catName : Name) : CompileM PUnit := do
  let ref ← getRef
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let some cat := cats.find? catName
    | throwError "cannot compile unknown category `{catName}`"
  withStepTrace (``Parser.Category ++ catName) (collapsed := true) do
  if (← checkOrMarkVisited catName) then
    return
  let mut leadingPs := #[]
  let mut trailingPs := #[]
  for (k, _) in cat.kinds do
    let pName := catName ++ stripUpperPrefix k
    modify fun s => {s with compiled := s.compiled.insert pName}
    let pId := mkIdentFrom ref pName
    let name ← resolveGlobalConstNoOverload (mkIdentFrom ref k)
    if let some alias := syntaxAliases.find? name then
      leadingPs := leadingPs.push pId
      pushAliasDef pName alias
    else
      let (trailing, p) ← withReader (fun _ => catName) do
        compileParserConst compileParserCat name
      if trailing then
        trailingPs := trailingPs.push pId
      else
        leadingPs := leadingPs.push pId
      pushDef pName p
  let value ← ``(LParse.category $(quote catName) #[$[↑$leadingPs],*] #[$[↑$trailingPs],*])
  pushDef catName value

end

--------------------------------------------------------------------------------
/-! ## Compile Commands                                                      -/
--------------------------------------------------------------------------------

section
open Elab Command Term PrettyPrinter

syntax dry := "(" noWs &"dry" noWs ")"

scoped syntax "compile_parser_category " (dry)? ident : command
elab_rules : command | `(compile_parser_category $[$dry?]? $cat:ident) => do
  let defn := Lean.mkConst (``Parser.Category ++ cat.getId)
  discard <| liftTermElabM <| addTermInfo cat defn
  let defs ← compileParserCat cat.getId |>.run
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile.result] s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

scoped syntax "compile_parser " (dry)? ident (" as " ident)? : command
elab_rules : command | `(compile_parser $[$dry?]? $id $[as $root?]?) => do
  let name ← resolveGlobalConstNoOverload id
  let some info := (← getEnv).find? name
    | throwErrorAt id s!"unknown constant '{name}'"
  discard <| liftTermElabM <| addTermInfo id (mkConst name)
  let innerRoot := stripUpperPrefix name
  let defs ← CompileT.run do
    let (_, p) ← compileParserInfo compileParserCat info
    unless (← get).compiled.contains innerRoot do pushDef innerRoot p
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile.result] s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"
  let ns : Name := root?.getD id |>.getId.str "lParse"
  let outerRoot := root?.getD ns
  let cmd ← `(namespace $ns $cmd end $ns abbrev $outerRoot := $(ns ++ innerRoot))
  if dry?.isNone then withMacroExpansion (← getRef) cmd <| elabCommand cmd

end
