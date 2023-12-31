# Partax

Partax (Parser + Syntax) is a library of tools for manipulating Lean syntax and parser definitions. It currently provides two major features:
* Configurable commands to compile Lean syntax categories and parser definitions into something else.
* A monadic parser (`LParse`) for parsing Lean syntax without needing a whole Lean `Environment`.

Essentially, Partax allows users to compile builtin or custom Lean grammars into simple, runnable parsers that can then be used in libraries or executables without needed Lean symbols and meta code.

## Usage

Partax provides two configurable commands for compiling Lean syntax: `compile_parser_category` and `compile_parser`. The former compiles a top-level syntax category and the later compiles a specific parser definition (which may include nested categories). Each of these commands accept a `CompileConfig` configuration provided via an optional `with` clause term, which defaults to a configuration that produces `LParse` definitions. For example:

```lean
import Lean
import Partax

open scoped Partax

compile_parser Lean.Parser.Term.attributes => attrs -- with CompileConfig.lParse
#eval attrs.run' "@[instance high, inline]" -- TSyntax `Lean.Parser.Term.attributes

compile_parser_category prio -- with CompileConfig.lParse
#eval prio.run' "default + default" -- TSyntax `prio

open Lean Elab Command in -- 2000
#eval liftMacroM (m := CommandElabM) do
  match prio.run' "default + default" with
  | .ok stx => evalPrio stx
  | .error e => Macro.throwError e
```

If something goes wrong while compiling, Partax provides two custom trace classes, `trace.Partax.compile.step` and `trace.Partax.compile.result`, to view, respectively, the parser-by-parser steps of the compilation and the final produced definitions.

## Limitations & Future Work

There are a number of additional features planned for Partax, including:

* Support for antiquotations (e.g. `$(...)` in ``` `(...) ``` syntax).
* Better optimized `LParse` with caching, a syntax stack, and indexed category parsing.
* Formally verified well-formed parser results (e.g., well-formed nodes).
* More compilation customization and other test cases than `LParse`.
* Improved compilation performance (compiling large categories like `term` can currently take a few minutes).
* An extended `syntax` command (called `grammar`) that supports all standard Lean parser features.
