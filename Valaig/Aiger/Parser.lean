import Valaig.Aiger.Basic
import Std.Internal.Parsec
import Std.Data.Iterators

namespace Valaig
namespace Aiger.Parser

open Std.Internal.Parsec.ByteArray
open Std.Internal.Parsec

@[inline]
private def require {α : Type} (pred : α → Bool) (error : String) (parse : Parser α) : Parser α := do
  let n ← parse
  if !(pred n) then
    fail error
  return n

@[inline]
private def tryParse {α : Type} (parse : Parser α) : Parser (Option α) := do
    attempt (parse <&> Option.some) <|> pure Option.none

@[inline]
def parseNat : Parser Nat := do
  let first ← peek?
  let n ← digits
  if n ≠ 0 && first = '0'.toUInt8 then
    fail "non-zero digit expected"
  pure n

@[inline]
def skipNewline : Parser Unit :=
  skipByteChar '\n' <|> fail "newline expected"

@[inline]
def skipSpace : Parser Unit :=
  skipByteChar ' ' <|> fail "space expected"

@[inline]
def parseVariable : Parser Nat := parseNat

@[inline]
def parsePos : Parser Nat :=
  parseNat |> require (. > 0) "non-zero integer expected"

@[inline]
def parseLiteral : Parser Nat :=
  parsePos |> require (. &&& 1 = 0) "even integer literal expected"

structure Header where
  maxVar : Nat
  numInputs : Nat
  numLatches : Nat
  numOutputs : Nat
  numAnds : Nat
  numBads : Nat
  numConstraints : Nat
  numJustice : Nat
  numFairness : Nat
deriving Repr

def parseHeader : Parser (Header × Bool) := do
  let binary ←
    (attempt $ skipString "aig" *> pure true) <|>
    (attempt $ skipString "aag" *> pure false) <|>
    fail "aag or aig expected"

  let nextNat :=
    skipSpace *> parseNat <|> fail "integer expected"

  -- Aiger 1.9 fields are optional and don't all have to be provided
  let maybeNextNat := do
    if (← peek?) == '\n'.toUInt8 then
      return 0
    nextNat

  let header := {
    maxVar := ← nextNat,
    numInputs := ← nextNat,
    numLatches := ← nextNat
    numOutputs := ← nextNat
    numAnds := ← nextNat,
    numBads := ← maybeNextNat,
    numConstraints := ← maybeNextNat,
    numJustice := ← maybeNextNat,
    numFairness := ← maybeNextNat,
  }

  -- We don't do the newline parsing in maybeNextNat (as we want it to be
  -- seen by each non-matching parser) so do it here
  skipNewline
  return (header, binary)

@[inline]
def parseNLines {α : Type} (parse : Parser α) (n : Nat) : Parser (Array α) := do
  let mut lines := .emptyWithCapacity n
  for _ in [0:n] do
    lines := lines.push (← parse <* skipNewline)
  return lines

@[inline]
def parseVariables (n : Nat) : Parser (Array Nat) :=
  parseNLines parseVariable n

@[inline]
def parseSymbolLine : Parser String := do
  let type ← satisfy ("ilobcjf".contains $ Char.ofUInt8 .)
  let pos ← parseNat
  skipSpace
  let symb ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  let _ := type
  let _ := pos
  match String.fromUTF8? symb.toByteArray with
  | none => fail "Couldn't decode non UTF8 symbol"
  | some c => pure c

@[inline]
def parseCommentLine : Parser String := do
  let comment ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  -- TODO: This is a double copy
  match String.fromUTF8? comment.toByteArray with
  | none => fail "Couldn't decode non UTF8 comment"
  | some c => pure c

@[inline]
def parseCommentHeader : Parser Unit := do
  skipByteChar 'c'
  skipNewline

@[inline]
def parseComments : Parser (Array String) := 
  attempt (parseCommentHeader *> many parseCommentLine) <|> pure #[]

@[inline]
def parseLatch (binary : Bool) : Parser Unit := do
  if !binary then
    let latch ← parseLiteral
    skipSpace
  let next ← parseVariable
  let reset ← tryParse (skipSpace *> parseVariable)

  let _ := next
  let _ := reset
  pure ()

@[inline]
def parseLatches (binary : Bool) (n : Nat) : Parser (Array Unit) :=
  parseNLines (parseLatch binary) n

namespace ASCII

@[inline]
def parseGate : Parser Unit := do
  let lhs ← parseLiteral
  let rhs0 ← skipSpace *> parseVariable
  let rhs1 ← skipSpace *> parseVariable

  let _ := lhs
  let _ := rhs0
  let _ := rhs1
  pure ()

@[inline]
def parseGates (n : Nat) : Parser (Array Unit) :=
  parseNLines parseGate n

end ASCII

namespace Binary

@[unbox]
private structure DeltaVariableState (N : Type) [∀ n, OfNat N n] where
  var : N := 0
  shift : N := 0

@[inline]
def parseDeltaVariable : Parser Nat := do
  let state := {}

  -- Manually unroll the first 8 steps using u64 as this is most common and
  -- fits within U64, so is fast this way whereas doing it with nats is slow
  -- as the shift is only done within gmp
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat
  let (done, state) := step (← any).toUInt64 state; if done then return state.var.toNat

  -- The rest can be done with Nat
  let mut nstate := { var := state.var.toNat, shift := state.shift.toNat }
  repeat
    let (done, state) := step (← any).toNat nstate;
    nstate := state
  until done
  return nstate.var

where
  @[inline]
  step {N : Type} [∀ n, OfNat N n] [AndOp N] [ShiftLeft N] [Add N] [BEq N]
      (byte : N) (state : DeltaVariableState N) : Bool × DeltaVariableState N :=
    let masked := byte &&& 0x7f
    let var := state.var + (masked <<< state.shift)
    let shift := state.shift + 7
    let done := byte &&& 0x80 == 0
    (done, { var, shift })

-- Examples from the Aiger spec
/-- info: Except.ok 0 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x00].toByteArray

/-- info: Except.ok 127 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x7f].toByteArray

/-- info: Except.ok 128 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x80, 0x01].toByteArray

/-- info: Except.ok 258 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x82, 0x02].toByteArray

/-- info: Except.ok 16383 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0xff, 0x7f].toByteArray

/-- info: Except.ok 16387 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x83, 0x80, 0x01].toByteArray

/-- info: Except.ok 268435455 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0xff, 0xff, 0xff, 0x7f].toByteArray

/-- info: Except.ok 268435463 -/
#guard_msgs in
#eval! parseDeltaVariable.run [0x87, 0x80, 0x80, 0x80, 0x01].toByteArray

@[inline]
def parseGate : Parser Unit := do
  let rhs0 ← parseDeltaVariable
  let rhs1 ← parseDeltaVariable
  pure ()

@[inline]
def parseGates (n : Nat) : Parser (Array Unit) := do
  let mut gates := .emptyWithCapacity n
  for _ in [0:n] do
    gates := gates.push (← parseGate)
  return gates

end Binary

def parse : Parser Unit := do
  let (header, binary) ← parseHeader
  if header.numFairness > 0 || header.numJustice > 0 then
    fail "Justice and Fairness properties not yet supported"

  if !binary then
    let inputs ← parseNLines parseLiteral header.numInputs

  let latches ← parseLatches binary header.numLatches
  let outputs ← parseVariables header.numOutputs
  let bads ← parseVariables header.numBads
  let constraints ← parseVariables header.numConstraints
  -- let justice
  -- let fairness

  let gates ←
    if binary then Binary.parseGates header.numAnds
    else            ASCII.parseGates header.numAnds

  let symbols ← many (attempt parseSymbolLine)
  let comments ← parseComments
  eof

end Aiger.Parser
end Valaig
