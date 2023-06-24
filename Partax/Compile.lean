/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Parser.Basic
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Lean.Meta.Eval
import Partax.LParse
import Partax.Trace

open Lean

namespace Partax

--------------------------------------------------------------------------------
/-! ## Evaluation Helpers                                                     -/
--------------------------------------------------------------------------------

@[inline] unsafe def unsafeEvalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr :=
  env.evalConst ParserDescr opts name

@[implemented_by unsafeEvalParserDescr] opaque evalParserDescr
(name : Name) (env : Environment) (opts : Options) : Except String ParserDescr

@[implemented_by Lean.Meta.evalExpr']
opaque evalExpr' (α) (typeName : Name) (value : Expr) (safety := DefinitionSafety.safe) : MetaM α

--------------------------------------------------------------------------------
/-! ## Compile Configuration                                                  -/
--------------------------------------------------------------------------------

/-
Dummy helpers just for WIP testing purposes
-/
namespace LParse

def term : LParse Term :=
  LParse.category `term #[ident, numLit, strLit] #[]

def decimal : LParse Syntax := atomOf do
  skipMany digit

@[inline] def dummy (errMsg : String := "dummy parser") : LParse Syntax := do
  fail errMsg

end LParse

def aliases :=
  ({} : NameMap Name)
  |>.insert `atomic ``atomic
  |>.insert `optional ``LParse.optional
  |>.insert `group ``LParse.group
  |>.insert `many ``LParse.manySyntax
  |>.insert `many1 ``LParse.many1Syntax
  |>.insert `sepByIndentSemicolon ``LParse.sepByIndentSemicolon
  |>.insert `sepBy1IndentSemicolon ``LParse.sepBy1IndentSemicolon
  |>.insert `num ``LParse.numLit
  |>.insert `str ``LParse.strLit
  |>.insert `ident ``LParse.ident
  |>.insert `hole ``LParse.hole
  |>.insert `withPosition ``LParse.withPosition
  |>.insert `withoutPosition ``LParse.withoutPosition
  |>.insert `colGe ``LParse.checkColGe
  |>.insert `colGt ``LParse.checkColGt
  |>.insert `colEq ``LParse.checkColEq
  |>.insert `ws ``LParse.checkWsBefore
  |>.insert `noWs ``LParse.checkNoWsBefore
  |>.insert `ppSpace ``LParse.nop
  |>.insert `ppDedent ``id
  |>.insert `ppLine ``LParse.nop
  |>.insert `patternIgnore ``id
  -- Placeholders
  |>.insert `term ``LParse.term
  |>.insert `decimal ``LParse.decimal
  |>.insert `tacticSeq ``LParse.dummy

def parserAliases :=
  ({} : NameMap Name)
  |>.insert ``Parser.ident ``LParse.ident
  |>.insert ``Parser.strLit ``LParse.strLit
  |>.insert ``Parser.numLit ``LParse.numLit
  |>.insert ``Parser.symbol ``LParse.symbol
  |>.insert ``Parser.nonReservedSymbol ``LParse.nonReservedSymbol
  |>.insert ``Parser.leadingNode ``LParse.leadingNode
  |>.insert ``Parser.atomic ``atomic
  |>.insert ``Parser.optional ``LParse.optional
  |>.insert ``Parser.many ``LParse.manySyntax
  |>.insert ``Parser.many1 ``LParse.many1Syntax
  |>.insert ``Parser.checkPrec ``LParse.checkPrec
  |>.insert ``Parser.withPosition ``LParse.withPosition
  |>.insert ``Parser.withoutPosition ``LParse.withoutPosition
  |>.insert ``Parser.checkColGe ``LParse.checkColGe
  |>.insert ``Parser.checkColGt ``LParse.checkColGt
  |>.insert ``Parser.checkColEq ``LParse.checkColEq
  |>.insert ``Parser.checkWsBefore ``LParse.checkWsBefore
  |>.insert ``Parser.checkNoWsBefore ``LParse.checkNoWsBefore
  |>.insert ``Parser.checkLinebreakBefore ``LParse.checkLinebreakBefore

--------------------------------------------------------------------------------
/-! ## Compile Functions                                                      -/
--------------------------------------------------------------------------------

local instance : Coe Name Ident where
  coe := mkIdent

def stripUpperPrefix : Name → Name
| .anonymous => .anonymous
| .str p s => if s.get 0 |>.isUpper then .anonymous else .str (stripUpperPrefix p) s
| .num p n => .num (stripUpperPrefix p) n

section
open Meta Elab Term Command Syntax Parser

structure CompileState where
  compiled : NameSet := .empty
  defs : Array Command := #[]

abbrev CompileT m := ReaderT Name <| StateT CompileState m
def CompileT.run [Functor m] (x : CompileT m α) : m (Array Command) :=
  StateT.run (ReaderT.run x .anonymous) {} <&> (·.2.defs)

abbrev CompileM := CompileT CommandElabM

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

@[inline] def compileCatUse
(compileCat : Name → CompileM PUnit)
(catName : Name) (rbp : Term) : CompileM Term := do
  if let some alias := aliases.find? catName then
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
      let env ← getEnv
      let some info := env.find? name
        | throwError s!"unknown constant '{name}'"
      let some numArgs ← checkParserType info
        | return mkCIdentFrom (← getRef) name
      if numArgs > 0 then
        throwError "cannot compile parameterized parser {name}"
      let pName := (← read) ++ stripUpperPrefix name
      if (← checkOrMarkVisited pName) then
        return mkIdentFrom (← getRef) pName
      let some p := info.value?
        | throwError "cannot compile opaque definition '{info.name}'"
      if p.isAppOf ``Parser.mk then
        throwError "cannot compile primitive parser '{name}'"
      let p ← compileExpr p
      pushDef pName p
      return mkIdentFrom (← getRef) pName
    | .app .. => do
      let fn := x.getAppFn; let args := x.getAppArgs
      if let .const fname _ := fn then
        if fname = ``OfNat.ofNat then
          return quote args[1]!.natLit?.get!
        else if (``Name).isPrefixOf fname then
          let name ← liftTermElabM <| liftMetaM do
            evalExpr' Name ``Name x
          return quote name
        else if fname = ``categoryParser then
          let catName ← liftTermElabM <| liftMetaM do
            evalExpr' Name ``Name args[0]!
          let rbp ← compileExpr args[1]!
          let use ← compileCatUse compileCat catName rbp
          return use
        else if fname = ``withCache || fname = ``withAntiquot then
          return ← compileExpr args[1]!
        else if fname = ``HAndThen.hAndThen then
          let p1 ← compileExpr args[4]!
          let p2 ← compileExpr args[5]!.bindingBody!
          return (← `($p1 >> $p2))
        else if fname = ``HOrElse.hOrElse then
          let p1 ← compileExpr args[4]!
          let p2 ← compileExpr args[5]!.bindingBody!
          return (← `($p1 <|> $p2))
        else if let some alias := parserAliases.find? fname then
          let args ← args.mapM compileExpr
          return mkApp (mkCIdentFrom (← getRef) alias) args
        else
          let some info := (← getEnv).find? fname
            | throwError "unknown constant '{fname}'"
          if let some numArgs ← checkParserType info then
            if numArgs = args.size then
              let some pLam := info.value?
                | throwError "cannot compile opaque definition '{info.name}'"
              let value := pLam.beta args
              if value.isAppOf ``Parser.mk then
                throwError "cannot compile primitive parser '{fname}'"
              return (← compileExpr value)
      let fn ← compileExpr fn
      let args ← args.mapM compileExpr
      return mkApp fn args
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

def compileParserDescr
(compileCat : Name → CompileM PUnit) (descr : ParserDescr) : CompileM Term :=
  compileDescr descr
where
  compileDescr
  | .const name => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    return mkCIdentFrom (← getRef) alias
  | .unary name p => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    let p ← compileDescr p
    return mkApp (mkCIdentFrom (← getRef) alias) #[p]
  | .binary name p1 p2 => do
    let p1 ← compileDescr p1
    let p2 ← compileDescr p2
    if name = `andthen then
      `($p1 >> $p2)
    else if name = `orelse then
      `($p1 <|> $p2)
    else
      let some alias := aliases.find? name
        | throwError s!"no parser alias defined for alias `{name}`"
      return mkApp (mkCIdentFrom (← getRef) alias) #[p1, p2]
  | .node kind prec p => do
    let p ← compileDescr p
    ``(LParse.leadingNode $(quote kind) $(quote prec) $p)
  | .trailingNode kind prec lhsPrec p => do
    let p ← compileDescr p
    ``(LParse.trailingNode $(quote kind) $(quote prec) $(quote lhsPrec) $p)
  | .symbol val => do
    ``(LParse.symbol $(quote val.trim))
  | .nonReservedSymbol val includeIdent => do
    ``(LParse.nonReservedSymbol $(quote val.trim) $(quote includeIdent))
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
  | .sepBy p _sep psep allowTrailingSep => do
    let p ← compileDescr p
    let s ← compileDescr psep
    ``(LParse.sepBy $p $s $(quote allowTrailingSep))
  | .sepBy1 p _sep psep allowTrailingSep => do
    let p ← compileDescr p
    let s ← compileDescr psep
    ``(LParse.sepBy1 $p $s $(quote allowTrailingSep))

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
  | _ => throwError "expected Parser or ParserDescr at '{info.name}'"

def compileParserConst
(compileCat : Name → CompileM PUnit)
(name : Name) : CompileM (Bool × Term) := do
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
  if (← checkOrMarkVisited catName) then
    return
  let mut leadingPs := #[]
  let mut trailingPs := #[]
  for (k, _) in cat.kinds do
    let pName := catName ++ stripUpperPrefix k
    modify fun s => {s with compiled := s.compiled.insert pName}
    let pId := mkIdentFrom ref pName
    let name ← resolveGlobalConstNoOverload (mkIdentFrom ref k)
    if let some alias := aliases.find? name then
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

syntax "compile_parser_category " ident : command
elab_rules : command | `(compile_parser_category $cat) => do
  let defn := Lean.mkConst (``Parser.Category ++ cat.getId)
  discard <| liftTermElabM <| addTermInfo cat defn
  let defs ← compileParserCat cat.getId |>.run
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile] s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"
  withMacroExpansion (← getRef) cmd <| elabCommand cmd

syntax "compile_parser " ident (" as " ident)? : command
elab_rules : command | `(compile_parser $id $[as $root?]?) => do
  let name ← resolveGlobalConstNoOverload id
  let some info := (← getEnv).find? name
    | throwErrorAt id s!"unknown constant '{name}'"
  discard <| liftTermElabM <| addTermInfo id (mkConst name)
  let innerRoot := stripUpperPrefix name
  let defs ← CompileT.run do
    let (_, p) ← compileParserInfo compileParserCat info
    unless (← get).compiled.contains innerRoot do pushDef innerRoot p
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile] s!"\n{(← liftCoreM <| ppCommand cmd).pretty 90}"
  let ns : Name := root?.getD id |>.getId.str "lParse"
  let outerRoot := root?.getD ns
  let cmd ← `(namespace $ns $cmd end $ns abbrev $outerRoot := $(ns ++ innerRoot))
  withMacroExpansion (← getRef) cmd <| elabCommand cmd

end

set_option trace.Partax.compile true
compile_parser Parser.Syntax.atom
