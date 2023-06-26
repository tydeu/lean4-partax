/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
import Lean.Util.Trace

open Lean

namespace Partax

initialize
  registerTraceClass `Partax.compile
  registerTraceClass `Partax.compile.step true
  registerTraceClass `Partax.compile.result true
