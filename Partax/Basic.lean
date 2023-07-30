/-
Copyright (c) 2022-2023 Mac Malone. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.MonadBacktrack

namespace Partax

open Lean (MonadBacktrack saveState restoreState)

--------------------------------------------------------------------------------
/-! # Abstractions                                                            -/
--------------------------------------------------------------------------------

/-- A monad equipped with an input string and a cursor within it. -/
class MonadInput (m : Type → Type u) where
  getInput : m String
  getInputPos : m String.Pos
  setInputPos : String.Pos → m Unit

export MonadInput (getInput getInputPos setInputPos)

instance [MonadLift m n] [MonadInput m] : MonadInput n where
  getInput := liftM (m := m) getInput
  getInputPos := liftM (m := m) getInputPos
  setInputPos p := liftM (m := m) <| setInputPos p

/-- Class for monads that permit Lean-style unexpected/expected errors. -/
class ThrowUnexpected (m : Type u → Type v) where
  throwUnexpected {α} : String → List String → m α

instance [MonadLift m n] [ThrowUnexpected m] : ThrowUnexpected n where
  throwUnexpected u e := liftM (m := m) <| ThrowUnexpected.throwUnexpected u e

@[macro_inline] def throwUnexpected [ThrowUnexpected m] (msg : String) (expected : List String := []) : m α :=
  ThrowUnexpected.throwUnexpected msg expected

@[noinline] def unexpectedEOIMessage : String :=
  "unexpected end-of-input"

@[inline] def throwUnexpectedEOI [ThrowUnexpected m] (expected : List String := []) : m α :=
  throwUnexpected unexpectedEOIMessage expected

/--
A monad equipped with a `checkpoint` operation to save and restore state.

Thus, it is similar in purpose to `MonadBacktrack`, but does not
require the user to know what kind of state is being saved or restored.
-/
class MonadCheckpoint (m : Type u → Type v) where
  /-- The callback argument restores state of the monad to the checkpoint. -/
  checkpoint {α} : ((restore : m PUnit) → m α) → m α

export MonadCheckpoint (checkpoint)

instance [MonadBacktrack σ m] [Bind m] : MonadCheckpoint m where
  checkpoint f := saveState >>= fun s => f (restoreState s)

@[inline] def saveAndRestoreState [Monad m] [MonadBacktrack σ m] (r : σ) : m σ := do
  let s ← saveState; restoreState r; return s

/-- The `orElse` part of `Alternative`. Implies `OrElse (m α)`.
Exists because `MonadExcept` implies `MonadOrElse` but not `Alternative`,
and we cannot use `OrElse (m α)` in polymorphic `variable` declarations. -/
class MonadOrElse (m : Type u → Type v) where
  orElse {α} : m α → (Unit → m α) → m α

instance [MonadOrElse m] {α : Type v} : OrElse (m α) where
  orElse := MonadOrElse.orElse

instance [MonadExcept ε m] : MonadOrElse m where
  orElse := MonadExcept.orElse

instance [Alternative m] : MonadOrElse m where
  orElse := Alternative.orElse

--------------------------------------------------------------------------------
/-! ## Primitives                                                             -/
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadInput m]

/-- Check if the parser is at the end of input. -/
@[inline] def getIsEOI : m Bool := do
  return (← getInput).atEnd (← getInputPos)

/-- Get the character at the parser head. Does not check for end-of-input. -/
@[inline] def peek : m Char := do
  return (← getInput).get (← getInputPos)

/-- Advance the parser one character. Does not check for end-of-input. -/
@[inline] def skip : m Unit := do
  setInputPos <| (← getInput).next (← getInputPos)

/-- Returns the next character in the input. Does not check for end-of-input. -/
@[inline] def next : m Char := do
  let c ← peek; skip; return c

variable [ThrowUnexpected m]

/-- Throw if not at end-of-input. -/
@[inline] def checkEOI : m PUnit := do
  unless (← getIsEOI) do
    throwUnexpected s!"unexpected '{← peek}'" ["end-of-input"]

/-- Throw if at end-of-input. -/
@[inline] def checkNotEOI (expected : List String := []) : m PUnit := do
  if (← getIsEOI) then throwUnexpectedEOI expected

/-- Invoke `f` with a proof that the parser head is not at end-of-input. -/
@[inline] def withNotEOI
(f : (input : String) → (pos : String.Pos) → ¬ input.atEnd pos → m α)
(expected : List String := [])  : m α := do
  let input ← getInput
  let inputPos ← getInputPos
  if h : input.atEnd inputPos then
    throwUnexpectedEOI expected
  else
    f input inputPos h

/-- Get the character at the parser head. Throws on end-of-input.  -/
@[inline] def peek1 (expected : List String := [])  : m Char := do
  withNotEOI (fun input pos h => return input.get' pos h) expected

/-- Advance the parser one character. Throws on end-of-input.  -/
@[inline] def skip1 (expected : List String := [])  : m PUnit := do
  withNotEOI (fun input pos h => setInputPos <| input.next' pos h) expected

/-- Returns the next character in the input. Throws on end-of-input.  -/
@[inline] def next1 (expected : List String := []) : m Char := do
  withNotEOI (expected := expected) fun input pos h =>  do
    setInputPos <| input.next' pos h
    return input.get' pos h

end

--------------------------------------------------------------------------------
/-! ## Extractors                                                             -/
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadInput m]

@[inline] def withString (p : m α) : m (String × α) := do
  let startPos ← getInputPos
  let a ← p
  let str := (← getInput).extract startPos (← getInputPos)
  return (str, a)

@[inline] def extract (p : m α) : m String :=
  (·.1) <$> withString p

@[inline] def withSubstring (p : m α) : m (Substring × α) := do
  let startPos ← getInputPos
  let a ← p
  let str := (← getInput).toSubstring.extract startPos (← getInputPos)
  return (str, a)

@[inline] def extractSub (p : m α) : m Substring :=
  (·.1) <$> withSubstring p

end

--------------------------------------------------------------------------------
/-! # Checkpoints                                                             -/
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadCheckpoint m]

/-- Apply `p` and backtrack unless it errors. -/
@[inline] def lookahead (p : m α) : m PUnit :=
  checkpoint fun restore => p *> restore

variable [MonadExcept ε m]

/-- Apply `p`, backtrack, and return whether `p` succeeded. -/
@[inline] def isFollowedBy (p : m α) : m Bool :=
  checkpoint fun restore => try p *> pure true catch _ => restore; pure false

/-- Error with `msg` if `isFollowedBy p`. -/
@[inline] def notFollowedBy [ThrowUnexpected m] (p : m α) (msg : String) : m PUnit := do
  if (← isFollowedBy p) then throwUnexpected msg

/--
Apply `p` as a single atomic parser.
On any failure within it, the parser state is reverted back to before `p`,
and the error is re-thrown. -/
@[inline] def atomic (p : m α) : m α :=
  checkpoint fun restore => try p catch e => restore *> throw e

variable [MonadInput m]

/--
Attempt to apply `p`.
If `p` errors without consuming input, revert the state and return `a`.
-/
@[inline] def attemptD  (a : α) (p : m α) : m α := do
  let iniPos ← getInputPos
  checkpoint fun restore =>
  try p catch e =>
    if iniPos < (← getInputPos) then
      throw e
    else
      restore
      return a

/-- Attempt to apply `p`. Return whether `p` succeeded. -/
@[inline] def attempt (p : m α) : m Bool :=
  attemptD false <| Functor.mapConst true p

/-- Attempt to apply `p`. On failure, returns `none`. -/
@[inline] def attempt? (p : m α) : m (Option α) :=
  attemptD none <| some <$> p

end

--------------------------------------------------------------------------------
/-! ## Other Combinators                                                      -/
--------------------------------------------------------------------------------

section
variable [Monad m]

@[inline] def andthen (p1 : m α) (p2 : m β) : m (α × β) := do
  return (← p1, ← p2)

@[inline] def choice [MonadOrElse m] (ps : Array (m α)) (h : ps.size > 0) : m α := do
  ps.toSubarray.popFront.foldr (· <|> ·) ps[0]

variable [MonadCheckpoint m] [MonadExcept ε m] [MonadInput m]

@[specialize] partial def collectManyCore (p : m α) (acc : Array α) : m (Array α) := do
  if let some a ← attempt? p then collectManyCore p (acc.push a) else pure acc

@[inline] def collectMany (p : m α) : m (Array α) :=
  collectManyCore p #[]

@[inline] def collectMany1 (p : m α) : m (Array α) := do
  let a ← p; collectManyCore p #[a]

@[specialize] partial def skipMany (p : m α) : m PUnit := do
  if (← attempt p) then skipMany p

@[inline] def skipMany1 (p : m α) : m PUnit :=
  p *> skipMany p

end

--------------------------------------------------------------------------------
/-! ## Character/Substring Matching                                           -/
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadInput m] [ThrowUnexpected m]

/-- Skip over a substring `str` in the input. -/
@[inline] def skipString (str : String) : m PUnit := do
  let input ← getInput
  let substr := Substring.mk input (← getInputPos) input.endPos |>.take str.length
  setInputPos substr.stopPos
  unless substr == str.toSubstring do
    throwUnexpected s!"unexpected '{substr}'" [s!"'{str}'"]

/-- Take the head character if its satisfies `p`. Otherwise, throw an error. -/
@[inline] def satisfy (p : Char → Bool) (expected : List String := []) : m Char := do
  withNotEOI (expected := expected) fun input pos h => do
    let c := input.get' pos h
    if p c then
      setInputPos <| input.next' pos h
      return c
    else
      throwUnexpected s!"unexpected '{c}'" expected

/-- Consume the head character if its satisfies `p`. Otherwise, throw an error. -/
@[inline] def skipSatisfy (p : Char → Bool) (expected : List String := []) : m PUnit :=
  discard <| satisfy p expected

/--
Consume the head character if its satisfies `p`.
Returns whether it succeeded. Throws on end-of-input.
-/
@[inline] def trySatisfy (p : Char → Bool) (expected : List String := []) : m Bool := do
  withNotEOI (expected := expected) fun input pos h => do
    if p <| input.get' pos h then
      setInputPos <| input.next' pos h
      return true
    else
      return false

/-- Consume the head character if its satisfies `p`. Throws on end-of-input. -/
@[inline] def skipIfSatisfy (p : Char → Bool) (expected : List String := []) : m PUnit := do
  discard <| trySatisfy p expected

/-- Consume the characters until one matches `p`. Does not consume the matched character. -/
@[specialize] partial def skipToSatisfy (p : Char → Bool) (expected : List String := []) : m PUnit := do
  withNotEOI (expected := expected) fun input pos h => do
    unless p <| input.get' pos h do
      setInputPos <| input.next' pos h
      skipToSatisfy p

/-- Consume characters until one matches `p`. Consumes the matched character. -/
@[specialize] partial def skipTillSatisfy (p : Char → Bool) (expected : List String := []) : m PUnit := do
  let c ← next1 expected; unless p c do skipTillSatisfy p

/-- Skip over a character `c` in the input. -/
@[inline] def skipChar (c : Char) : m PUnit :=
  skipSatisfy (· = c) [s!"'{c}'"]

/-- Consume characters until one matches `c`. Consumes the matched character. -/
@[inline] def skipTillChar (c : Char) : m PUnit := do
  skipTillSatisfy (· = c) [s!"terminating '{c}'"]

/-- Matches a single whitespace character (i.e. `Char.isWhitespace`). -/
@[inline] def wsChar : m Char := do
  satisfy Char.isWhitespace ["whitespace character"]

/-- Skip over whitespace characters in the input. -/
@[inline] def skipWs [MonadCheckpoint m] [MonadExcept ε m] : m Unit := do
  skipMany wsChar

/-- Matches a single binary digit (bit). -/
@[inline] def bit : m Char := do
  satisfy (fun c => c = '0' ∨ c = '1') ["binary digit"]

/-- Matches a single octal digit (0-7). -/
@[inline] def octDigit : m Char := do
  satisfy (fun c => '0' ≤ c ∧ c ≤ '7') ["octal digit"]

/-- Matches a single decimal digit. -/
@[inline] def digit : m Char := do
  satisfy (fun c => '0' ≤ c ∧ c ≤ '9') ["digit"]

/-- Matches a single upper- or lower-case hexadecimal digit. -/
@[inline] def hexDigit : m Char := do
  satisfy (expected := ["hex digit"]) fun c =>
    ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

end

--------------------------------------------------------------------------------
/-! ## Longest Match                                                          -/
--------------------------------------------------------------------------------

/--
Tries all parsers in `ps`, searching for the last longest match.
If the last longest match succeeded, restore its state and return its result.
Otherwise, merge the errors of all failing longest match parsers into one error
and throw it, restoring the state of the last erroring longest match parser.
-/
@[inline] def longestMatch
[Monad m] [MonadInput m] [MonadExcept ε m] [MonadBacktrack σ m]
(ps : Array (m α)) (h : ps.size > 0) (mergeErrors : ε → ε → ε) : m α := do
  let s0 ← saveState
  let rec @[specialize] loop (res : EStateM.Result ε σ α) (oldTail) (i) := do
    if h : i < ps.size then
      restoreState s0
      match (← observing ps[i]) with
      | .ok a =>
        let newTail := (← getInputPos).byteIdx
        if oldTail ≤ newTail then
          let s ← saveState
          loop (.ok a s) newTail (i+1)
        else
          loop res oldTail (i+1)
      | .error e2 =>
        let newTail := (← getInputPos).byteIdx
        if oldTail ≤ newTail then
          match res with
          | .ok .. => loop res oldTail (i+1)
          | .error e1 _ =>
            let s2 ← saveState
            if oldTail = newTail then
              loop (.error (mergeErrors e1 e2) s2) newTail (i+1)
            else
              loop (.error e2 s2) newTail (i+1)
        else
          loop res oldTail (i+1)
    else
      match res with
      | .ok a s => restoreState s *> pure a
      | .error e s => restoreState s *> throw e
  let x ← observing ps[0]
  let tail := (← getInputPos).byteIdx
  let s ← saveState
  match x with
  | .ok a => loop (.ok a s) tail 1
  | .error e => loop (.error e s) tail 1
termination_by loop _ _ i => ps.size - i
