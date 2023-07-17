/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Partax
import Lean.Parser

open Lean

namespace Partax.Test

/-! # Test Utilities -/

def flipExcept : Except ε α → Except α ε
| .ok a => .error a
| .error e => .ok e

instance [ToString ε] [ToString α] : Eval (Except ε α) where
  eval f _ :=
    match f () with
    | .ok a => IO.print <| toString a
    | .error e => throw <| IO.userError <| toString e

open Parser in
@[scoped command_parser] def matchStx := leading_parser
  "#match_stx " >> ident >> termParser >> " | " >> parserOfStack 2

open Syntax in
partial def quoteSyntax : Syntax → Term
| .missing => mkCIdent ``missing
| .atom _ val => mkCApp ``mkAtom #[quote val]
| .ident _ _ val _  => mkCApp ``mkIdent #[quote val]
| .node _ kind args =>
    let args := Unhygienic.run `(#[$(args.map quoteSyntax),*])
    mkCApp ``mkNode #[quote kind, args]

def matchStxFn (pstx : Syntax) (stx : Syntax) : Except String Syntax := do
  if pstx == stx then return pstx
  throw <| s!"parsed:\n{pstx}\nexpected:\n{stx}\n"

@[inline] def Macro.undefinedGlobalName (name : Name) : MacroM Bool := do
  return (← Macro.resolveGlobalName name).filter (·.2.isEmpty) |>.isEmpty

@[macro matchStx] def expandMatchStx : Macro := fun matchStx => do
  let p : Ident := ⟨matchStx[2]⟩; let stx := matchStx[4]
  let some src := stx.updateTrailing "".toSubstring |>.reprint
    | Macro.throwError "cannot reprint syntax"
  let kwsName := p.getId ++ `keywords
  let catsName := p.getId ++ `categories
  let test ← `((matchStxFn · $(quoteSyntax stx)))
  if (← Macro.undefinedGlobalName catsName) then
    `(#eval $(p).run $(quote src) >>= $test)
  else
    let kws := mkIdentFrom p kwsName
    let cats := mkIdentFrom p catsName
    `(#eval $(p).run $(quote src) (cats := $cats) (kws := $kws) >>= $test)
