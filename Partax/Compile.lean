/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Parser.Basic
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Partax.Parsec

open Lean Elab Term Syntax Parser Command

namespace Partax

unsafe def unsafeEvalParserDescr
(env : Environment) (opts : Options) (name : Name) : Except String (ParserDescr × Bool) :=
  if let some info := env.find? name then
    match info.type with
    | Expr.const c _ =>
      match c with
      | ``ParserDescr =>
        env.evalConst ParserDescr opts name <&> (·, false)
      | ``TrailingParserDescr =>
        env.evalConst TrailingParserDescr opts name <&> (·, true)
      | _ => throw <| s!"expected ParserDescr at '{name}'"
    | _ => throw <| s!"expected ParserDescr at '{name}'"
  else
    throw <| s!"unknown constant '{name}'"

@[implemented_by unsafeEvalParserDescr] opaque evalParserDescr
(env : Environment) (opts : Options) (name : Name) : Except String (ParserDescr × Bool)

@[inline] def Parsec.dummy (errMsg : String := "dummy parser") : Parsec Syntax := do
  throw {unexpected := errMsg}

def aliases :=
  ({} : NameMap Name)
  |>.insert `atomic ``Parsec.atomic
  |>.insert `orelse ``ParsecOrElse.orElse
  |>.insert `andthen ``ParsecAndThen.andThen
  |>.insert `optional ``Parsec.optional
  |>.insert `group ``Parsec.group
  |>.insert `many ``Parsec.many
  |>.insert `many1 ``Parsec.many1
  |>.insert `sepByIndentSemicolon ``Parsec.sepByIndentSemicolon
  |>.insert `sepBy1IndentSemicolon ``Parsec.sepBy1IndentSemicolon
  |>.insert `num ``Parsec.num
  |>.insert `ident ``Parsec.ident
  |>.insert `hole ``Parsec.hole
  |>.insert `withPosition ``Parsec.withPosition
  |>.insert `withoutPosition ``Parsec.withoutPosition
  |>.insert `checkColGe ``Parsec.checkColGe
  |>.insert `checkColGt ``Parsec.checkColGt
  |>.insert `checkColEq ``Parsec.checkColEq
  |>.insert `colGe ``Parsec.checkColGe
  |>.insert `colGt ``Parsec.checkColGt
  |>.insert `colEq ``Parsec.checkColEq
  |>.insert `ppSpace ``Parsec.nop
  |>.insert `ppDedent ``id
  |>.insert `ppLine ``Parsec.nop
  |>.insert `patternIgnore ``id
  -- Placeholders
  |>.insert `term ``Parsec.term
  |>.insert `decimal ``Parsec.decimal
  |>.insert ``Priority.numPrio ``Parsec.num
  |>.insert `tacticSeq ``Parsec.dummy
  |>.insert ``Tactic.Conv.dsimp ``Parsec.dummy
  |>.insert ``Tactic.Conv.simp ``Parsec.dummy

instance : Coe Name Ident where
  coe := mkIdent

partial def compileParserDescr
(ref : Syntax) (ns : Name) (cats : ParserCategories) (descr : ParserDescr)
: CommandElabM (Term × Array Command) :=
  StateT.run' (s := NameSet.empty) do compileDescr descr
where
  mkDef (name : Name) (value : Term) : Command :=
    Unhygienic.run do withRef ref `(partial def $name := $value)
  mkInlineDef (name : Name) (value : Term) : Command :=
    Unhygienic.run do withRef ref `(@[inline] partial def $name  := $value)
  compileDescr
  | .const name => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    return (mkCIdentFrom ref alias, {})
  | .unary name p => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    let (p, defs) ← compileDescr p
    let value := mkApp (mkCIdentFrom ref alias) #[p]
    return (value, defs)
  | .binary name p1 p2 => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    let (p1, defs1) ← compileDescr p1
    let (p2, defs2) ← compileDescr p2
    let value := mkApp (mkCIdentFrom ref alias) #[p1, p2]
    return (value, defs1.append defs2)
  | .node kind prec p => do
    let (p, defs) ← compileDescr p
    let value ← ``(Parsec.leadingNode $(quote kind) $(quote prec) $p)
    return (value, defs)
  | .trailingNode kind prec lhsPrec p => do -- Does not really work (missing LHS)
    let (p, defs) ← compileDescr p
    let value ← ``(Parsec.trailingNode $(quote kind) $(quote prec) $(quote lhsPrec) $p)
    return (value, defs)
  | .symbol val => do
    let value ← ``(Parsec.atom $(quote val.trim))
    return (value, {})
  | .nonReservedSymbol val _includeIdent => do
    let value ← ``(Parsec.atom $(quote val.trim))
    return (value, {})
  | .cat catName rbp => do -- Requires `partial`
    if let some alias := aliases.find? catName then
      return (mkCIdentFrom ref alias, {})
    else if let some cat := cats.find? catName then
      let mut ps := #[]
      let mut defs := #[]
      let cName := ns ++ catName
      unless (← get).contains catName do
        modify (·.insert catName)
        for (k, _) in cat.kinds do
          let pName := cName ++ k
          ps := ps.push <| mkIdentFrom ref pName
          let name ← resolveGlobalConstNoOverload (mkIdentFrom ref k)
          if let some alias := aliases.find? name then
            defs := defs.push <| mkInlineDef pName (mkCIdentFrom ref alias)
          else
            let (descr, _) ← IO.ofExcept <| evalParserDescr (← getEnv) (← getOptions) name
            let (p, pdefs) ← compileDescr descr
            defs := defs.append pdefs
            defs := defs.push <| mkDef pName p
        let qps ← ps.foldlM (``(Array.push $(·) $(·))) (← ``(Array.empty))
        let value ← ``(Parsec.category $(quote catName) $qps)
        defs := defs.push <| mkDef cName value
      let value ← ``(Parsec.withPrec $(quote rbp) $cName)
      return (value, defs)
    else
      throwError s!"no parser alias defined for unknown category `{catName}`"
  | .parser name => do -- Alias only
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for parser `{name}`"
    return (mkCIdentFrom ref alias, {})
  | .nodeWithAntiquot _name kind p => do -- No antiquote support
    let nName := ns ++ kind
    let (p, defs) ← compileDescr p
    let value ← ``(Parsec.node $(quote kind) ↑$p)
    if (← get).contains nName then
      return (mkIdent nName, defs)
    else
      modify (·.insert nName)
      let defs := defs.push <| mkDef nName value
      return (mkIdent nName, defs)
  | .sepBy p _sep psep allowTrailingSep => do
    let (p, pdefs) ← compileDescr p
    let (s, sdefs) ← compileDescr psep
    let defs := pdefs.append sdefs
    let value ← ``(Parsec.sepBy $p $s $(quote allowTrailingSep))
    return (value, defs)
  | .sepBy1 p _sep psep allowTrailingSep => do
    let (p, pdefs) ← compileDescr p
    let (s, sdefs) ← compileDescr psep
    let defs := pdefs.append sdefs
    let value ← ``(Parsec.sepBy1 $p $s $(quote allowTrailingSep))
    return (value, defs)

elab "compile_parser_descr " id:ident : command => do
  let ref ← getRef
  let name ← resolveGlobalConstNoOverload id
  let (descr, _) ← IO.ofExcept <| evalParserDescr (← getEnv) (← getOptions) name
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let root := name.str "parsec"
  let (p, defs) ← compileParserDescr ref root cats descr
  let defs := defs.push <| ← `(@[inline] partial def $root := $p)
  let cmd ← `(mutual $defs* end)
  dbg_trace (← liftCoreM <| PrettyPrinter.ppCommand cmd)
  withMacroExpansion ref cmd <| elabCommand cmd

elab "compile_parser_category " cat:ident " in " root:ident : command => do
  let ref ← getRef
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let (_, defs) ← compileParserDescr ref root.getId cats (.cat cat.getId 0)
  let cmd ← `(mutual $defs* end)
  dbg_trace (← liftCoreM <| PrettyPrinter.ppCommand cmd)
  withMacroExpansion ref cmd <| elabCommand cmd
