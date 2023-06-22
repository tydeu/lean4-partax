/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Parser.Basic
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Partax.Parsec
import Partax.Trace

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

-- Just for testing purposes
namespace Parsec

def term : Parsec Term :=
  Parsec.category `term #[ident, num, str] #[]

def decimal : Parsec Syntax := atomOf do
  skipMany digit

@[inline] def dummy (errMsg : String := "dummy parser") : Parsec Syntax := do
  throw {unexpected := errMsg}

end Parsec

def aliases :=
  ({} : NameMap Name)
  |>.insert `atomic ``Parsec.atomic
  |>.insert `optional ``Parsec.optional
  |>.insert `group ``Parsec.group
  |>.insert `many ``Parsec.manySyntax
  |>.insert `many1 ``Parsec.many1Syntax
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

instance : Coe Name Ident where
  coe := mkIdent

def stripUpperPrefix : Name → Name
| .anonymous => .anonymous
| .str p s => if s.get 0 |>.isUpper then .anonymous else .str (stripUpperPrefix p) s
| .num p n => .num (stripUpperPrefix p) n

open Parsec in
partial def compileParserDescr
(ref : Syntax) (rootNs : Name) (cats : ParserCategories) (descr : ParserDescr)
: CommandElabM (Term × Array Command) :=
  StateT.run' (s := NameSet.empty) do compileDescr rootNs descr
where
  mkDef (name : Name) (value : Term) : Command :=
    Unhygienic.run do withRef ref `(partial def $name := $value)
  mkInlineDef (name : Name) (value : Term) : Command :=
    Unhygienic.run do withRef ref `(@[inline] partial def $name  := $value)
  compileDescr ns
  | .const name => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    return (mkCIdentFrom ref alias, {})
  | .unary name p => do
    let some alias := aliases.find? name
      | throwError s!"no parser alias defined for alias `{name}`"
    let (p, defs) ← compileDescr ns p
    let value := mkApp (mkCIdentFrom ref alias) #[p]
    return (value, defs)
  | .binary name p1 p2 => do
    let (p1, defs1) ← compileDescr ns p1
    let (p2, defs2) ← compileDescr ns p2
    let defs := defs1.append defs2
    if name = `andthen then
      return (← `($p1 >> $p2), defs)
    else if name = `orelse then
      return (← `($p1 <|> $p2), defs)
    else
      let some alias := aliases.find? name
        | throwError s!"no parser alias defined for alias `{name}`"
      let value := mkApp (mkCIdentFrom ref alias) #[p1, p2]
      return (value, defs)
  | .node kind prec p => do
    let (p, defs) ← compileDescr ns p
    let value ← ``(Parsec.leadingNode $(quote kind) $(quote prec) $p)
    return (value, defs)
  | .trailingNode kind prec lhsPrec p => do -- Does not really work (missing LHS)
    let (p, defs) ← compileDescr ns p
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
      let mut defs := #[]
      let mut leadingPs := #[]
      let mut trailingPs := #[]
      let cName := rootNs ++ catName
      unless (← get).contains catName do
        modify (·.insert catName)
        for (k, _) in cat.kinds do
          let pName := cName ++ stripUpperPrefix k
          let pId := mkIdentFrom ref pName
          let name ← resolveGlobalConstNoOverload (mkIdentFrom ref k)
          if let some alias := aliases.find? name then
            leadingPs := leadingPs.push pId
            defs := defs.push <| mkInlineDef pName (mkCIdentFrom ref alias)
          else
            let (descr, trailing) ← IO.ofExcept <| evalParserDescr (← getEnv) (← getOptions) name
            if trailing then
              trailingPs := trailingPs.push pId
            else
              leadingPs := leadingPs.push pId
            let (p, pdefs) ← compileDescr cName descr
            defs := defs.append pdefs
            defs := defs.push <| mkDef pName p
        let value ← ``(Parsec.category $(quote catName) #[$[↑$leadingPs],*] #[$[↑$trailingPs],*])
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
    let nName := ns ++ stripUpperPrefix kind
    let (p, defs) ← compileDescr ns p
    let value ← ``(Parsec.node $(quote kind) $p)
    if (← get).contains nName then
      return (mkIdent nName, defs)
    else
      modify (·.insert nName)
      let defs := defs.push <| mkDef nName value
      return (mkIdent nName, defs)
  | .sepBy p _sep psep allowTrailingSep => do
    let (p, pdefs) ← compileDescr ns p
    let (s, sdefs) ← compileDescr ns psep
    let defs := pdefs.append sdefs
    let value ← ``(Parsec.sepBy $p $s $(quote allowTrailingSep))
    return (value, defs)
  | .sepBy1 p _sep psep allowTrailingSep => do
    let (p, pdefs) ← compileDescr ns p
    let (s, sdefs) ← compileDescr ns psep
    let defs := pdefs.append sdefs
    let value ← ``(Parsec.sepBy1 $p $s $(quote allowTrailingSep))
    return (value, defs)

syntax "compile_parser_descr " ident (" as " ident)? : command
elab_rules : command | `(compile_parser_descr $id $[as $root?]?) => do
  let ref ← getRef
  let name ← resolveGlobalConstNoOverload id
  let (descr, _) ← IO.ofExcept <| evalParserDescr (← getEnv) (← getOptions) name
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let root := match root? with | some r => r.getId | none => id.getId.str "parsec"
  let (p, defs) ← compileParserDescr ref root cats descr
  let defs := defs.push <| ← `(@[inline] partial def $root := $p)
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile] s!"\n{(← liftCoreM <| PrettyPrinter.ppCommand cmd).pretty 90}"
  withMacroExpansion ref cmd <| elabCommand cmd

syntax "compile_parser_category " ident (" in " ident)? : command
elab_rules : command | `(compile_parser_category $cat $[in $root?]?) => do
  let ref ← getRef
  let root := match root? with | some id => id.getId | none => .anonymous
  let cats := Parser.parserExtension.getState (← getEnv) |>.categories
  let (_, defs) ← compileParserDescr ref root cats (.cat cat.getId 0)
  let cmd ← `(mutual $defs* end)
  trace[Partax.compile] s!"\n{(← liftCoreM <| PrettyPrinter.ppCommand cmd).pretty 90}"
  withMacroExpansion ref cmd <| elabCommand cmd
