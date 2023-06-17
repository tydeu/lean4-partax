/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under the MIT license.
Authors: Mac Malone
-/
namespace Partax

--------------------------------------------------------------------------------
-- # Abstractions
--------------------------------------------------------------------------------

/-- A monad equipped with an input string and a cursor within it. -/
class MonadInput (m : Type → Type u) where
  getInput : m String
  getInputPos : m String.Pos
  setInputPos : String.Pos → m Unit

export MonadInput (getInput getInputPos setInputPos)

/-- Class for monads that permit Lean-style unexpected/expected errors. -/
class ThrowUnexpected (m : Type u → Type v) where
  throwUnexpected {α} : String → List String → m α

@[macro_inline] def throwUnexpected [ThrowUnexpected m] (msg : String) (expected : List String := []) : m α :=
  ThrowUnexpected.throwUnexpected msg expected

@[noinline] def unexpectedEOIMessage : String := "unexpected end of input"

@[inline] def throwUnexpectedEOI [ThrowUnexpected m] (expected : List String := []) : m α :=
  throwUnexpected unexpectedEOIMessage expected

/--
A monad equipped with a `checkpoint` operation to save and restore state.

Thus, it is similar in purpose to `EStateM.Backtrackable`, but does not
require the user to know what kind of state is being saved or restored.
-/
class MonadCheckpoint (m : Type u → Type v) where
  /-- The callback argument restores state of the monad to the checkpoint. -/
  checkpoint {α} : ((restore : m PUnit) → m α) → m α

export MonadCheckpoint (checkpoint)

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

namespace Parsec

--------------------------------------------------------------------------------
-- ## Primitives
--------------------------------------------------------------------------------

/-- A no-op parser. -/
@[always_inline, inline] def nop [Pure m] : m PUnit := pure ()

section
variable [Monad m] [MonadInput m]

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

/-- Throw if at end-of-input. -/
@[inline] def checkNotEOI : m PUnit := do
  if (← getInput).atEnd (← getInputPos) then throwUnexpectedEOI

/-- Advance the parser one character. Throws on end-of-input.  -/
@[inline] def skip1 : m PUnit := do
  checkNotEOI; skip

/-- Returns the next character in the input. Throws on end-of-input.  -/
@[inline] def anyChar : m Char := do
  checkNotEOI; next

end

--------------------------------------------------------------------------------
-- ## Extractors
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
-- # Checkpoints
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadCheckpoint m]

/--
Apply `p` as a single atomic parser.
On any failure within it, the parser state is reset back to before `p`,
and the error is re-thrown. -/
def atomic [MonadExcept ε m] (p : m α) : m α :=
  checkpoint fun restore => try p catch e => restore *> throw e

variable [MonadOrElse m]

/--
Attempts to apply `p` and returns whether it succeeded.
On failure, the parser state is reset back to before `p`. -/
@[inline] def attempt (p : m α) : m Bool :=
  checkpoint fun restore => p *> pure true <|> restore *> pure false

/-- Attempts to apply `p`, otherwise resets state and returns `a`.-/
@[inline] def attemptD (a : α) (p : m α) : m α :=
  checkpoint fun restore => p <|> restore *> pure a

/-- Attempts to apply `p`, otherwise resets state and returns `none`. -/
@[inline] def attempt? (p : m α) : m (Option α) :=
  attemptD none <| some <$> p

/-- Attempts to apply `p1`, otherwise resets state and applies `p2`. -/
@[inline] def attemptOrElse (p1 p2 : m α) : m α :=
  checkpoint fun restore => p1 <|> restore *> p2

end

--------------------------------------------------------------------------------
-- ## Other Combinators
--------------------------------------------------------------------------------

section
variable [Monad m]

@[inline] def andthen (p1 : m α) (p2 : m β) : m (α × β) := do
  return (← p1, ← p2)

variable [MonadOrElse m]

def choice [ThrowUnexpected m] (ps : Array (m α)) (errMsg := "unexpected empty choice") : m α := do
  if h : ps.size > 0 then
    ps.toSubarray.popFront.foldr (· <|> ·) ps[0]
  else
    throwUnexpected errMsg

variable [MonadCheckpoint m]

partial def manyCore (p : m α) (acc : Array α) : m (Array α) := do
  if let some a ← attempt? p then manyCore p (acc.push a) else pure acc

@[inline] def many (p : m α) : m (Array α) :=
  manyCore p #[]

@[inline] def many1 (p : m α) : m (Array α) := do
  let a ← p; manyCore p #[a]

@[inline] partial def skipMany (p : m α) : m PUnit := do
  if (← attempt p) then skipMany p else pure ()

@[always_inline, inline] def skipMany1 (p : m α) : m PUnit :=
  p *> skipMany p

end

--------------------------------------------------------------------------------
-- ## Character/Substring Matching
--------------------------------------------------------------------------------

section
variable [Monad m] [MonadInput m] [ThrowUnexpected m]

@[inline]
def skipString (str : String) : m PUnit := do
  let input ← getInput
  let substr := Substring.mk input (← getInputPos) input.endPos |>.take str.length
  if substr == str.toSubstring then
    setInputPos substr.stopPos
  else
    throwUnexpected s!"unexpected '{substr}'" [s!"'{str}'"]

@[always_inline, inline]
def satisfy (p : Char → Bool) (expected : List String := []) : m Char := do
  let c ← anyChar; if p c then return c else throwUnexpected s!"unexpected '{c}'" expected

@[always_inline, inline]
def skipSatisfy (p : Char → Bool) (expected : List String) : m PUnit :=
  discard <| satisfy p expected

/-- Consume characters until one matches `p`. Consumes the matched character. -/
@[inline] partial def skipTillSatisfy (p : Char → Bool) : m PUnit := do
  let c ← anyChar; if p c then pure () else skipTillSatisfy p

@[inline] def skipChar (c : Char) : m PUnit :=
  skipSatisfy (· = c) [s!"'{c}'"]

@[inline] def wsChar : m Char := do
  satisfy Char.isWhitespace ["whitespace character"]

@[inline] def skipWs [MonadCheckpoint m] [MonadOrElse m] : m Unit := do
  skipMany wsChar

@[inline] def bit : m Char := do
  satisfy (fun c => c = '0' ∨ c = '1') ["binary digit"]

@[inline] def octDigit : m Char := do
  satisfy (fun c => '0' ≤ c ∧ c ≤ '7') ["octal digit"]

@[inline] def digit : m Char := do
  satisfy (fun c => '0' ≤ c ∧ c ≤ '9') ["digit"]

@[inline] def hexDigit : m Char := do
  satisfy (expected := ["hex digit"]) fun c =>
    ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

end
