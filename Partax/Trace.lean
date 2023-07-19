/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Trace

open Lean

namespace Partax

initialize
  registerTraceClass `Partax.compile
  registerTraceClass `Partax.compile.step true
  registerTraceClass `Partax.compile.result true
