module

public import Valaig.Aiger.Parser.Defs
public import Std.Internal.Parsec

namespace Valaig.Aiger.Parser

open Std.Internal.Parsec.ByteArray
open Std.Internal.Parsec

section Parser

variable {BodyM : Type -> Type} [Monad BodyM] [MonadLiftT Parser BodyM] [MonadReaderOf Header BodyM]

-- Lean can't automatically convert out of Parsec to our type so we use this
@[inline]
def failM (msg : String) : BodyM α :=
  (Std.Internal.Parsec.fail msg : Parser _)

@[inline]
def tryParse {α : Type} (parse : Parser α) : Parser (Option α) := do
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

def parseHeader : Parser Header := do
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
    binary,
    maxVar := .ofIdx (←nextNat),
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
  return header

variable {α : Type}

@[inline]
def getHeader : BodyM Header :=
  read

@[inline]
def binary : BodyM Bool :=
  return (←getHeader).binary

namespace Binary

@[inline]
def firstInput : BodyM Var :=
  -- 0 is used for constant false
  return (Var.ofIdx 1)

@[inline]
def firstLatch : BodyM Var :=
  return (←firstInput) + (←getHeader).numInputs

@[inline]
def firstGate : BodyM Var :=
  return (←firstLatch) + (←getHeader).numLatches

end Binary

@[inline]
def asLit (n : Nat) : BodyM Lit := do
  let lit := .ofIdx n
  if lit.var > (←getHeader).maxVar then
    failM "literal exceeds maximum variable specified in header"
  return lit

-- Validates a literal used to define a gate/latch that must be even and non-zero
@[inline]
def asDefiningLit (n : Nat) : BodyM Var := do
  let lit ← asLit n
  if lit.isConstant then
    failM "non-zero integer literal expected"
  if lit.inverted then
    failM "even integer literal expected"
  pure lit.var

@[inline]
def parseLit : BodyM Lit :=
  parseNat >>= asLit

@[inline]
def parseDefiningLit : BodyM Var :=
  parseNat >>= asDefiningLit

@[inline]
def parseNLines {α : Type} (n : Nat) (parse : (idx : Nat) -> BodyM α) : BodyM (Array α) := do
  let mut arr := .emptyWithCapacity n
  for i in [0:n] do
    arr := arr.push (← parse i <* skipNewline)
  return arr

@[inline]
def parseDefiningLiterals {α : Type} (n : Nat) (f : Var -> α) : BodyM (Array α) :=
  parseNLines n <| fun _ => f <$> parseDefiningLit

@[inline]
def parseOutputLiterals (n : Nat) : BodyM (Array Output) :=
  parseNLines n <| fun _ => Output.mk <$> parseLit

@[inline]
def parseInputs : BodyM (Array Input) := do
  let n := (←getHeader).numInputs

  if (←binary) then
    let first ← Binary.firstInput
    return .ofFn fun (i : Fin n) => .mk (first + i.val)
  else
    parseDefiningLiterals n .mk

@[inline]
def parseLatch (n : Nat) : BodyM Latch := do
  let var ←
    match ←binary with
    | true => pure <| (←Binary.firstLatch) + n
    | false => parseDefiningLit <* skipSpace

  let next ← parseLit
  let reset ← (←tryParse (skipSpace *> parseNat)) |>.mapM asLit

  return { var, next, reset }

@[inline]
def parseLatches : BodyM (Array Latch) := do
  parseNLines (←getHeader).numLatches parseLatch

@[inline]
def parseSymbolLine : Parser Symbol := do
  let type : SymbolType ←
    match ← (any : Parser _) <&> Char.ofUInt8 with
    | 'i' => pure SymbolType.input
    | 'l' => pure SymbolType.latch
    | 'o' => pure SymbolType.output
    | 'b' => pure SymbolType.bad
    | 'c' => pure SymbolType.constraint
    | 'j' => pure SymbolType.justice
    | 'f' => pure SymbolType.fairness
    | c => fail s!"unsupported symbol type {c}"

  let idx ← parseNat
  let symb ←
    (attempt $ skipSpace *> takeUntil (. = '\n'.toUInt8)) <|>
    (pure ByteSlice.empty : Parser _)
  skipNewline

  match String.fromUTF8? symb.toByteArray with
  | none => fail "couldn't decode non-UTF8 symbol"
  | some sym => return ((type, idx), sym)

@[inline]
partial def parseSymbols : BodyM (Std.HashMap SymbolIndex String) := do
  let mut symbols := .emptyWithCapacity
  repeat
    match ← tryParse parseSymbolLine with
    | none => break
    | some (idx, symbol) =>
      let (contains, s) := symbols.containsThenInsert idx symbol
      symbols := s
      if contains then
        failM s!"symbol {repr idx} defined multiple times"
  return symbols

@[inline]
def parseCommentLine : Parser String := do
  let comment ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  match String.fromUTF8? comment.toByteArray with
  | none => fail "couldn't decode non-UTF8 comment"
  | some c => return c

@[inline]
def parseCommentHeader : Parser Unit := do
  skipByteChar 'c'
  skipNewline

@[inline]
partial def parseComments : Parser (Array String) :=
  attempt (parseCommentHeader *> many parseCommentLine) <|> pure #[]

namespace ASCII

@[inline]
def parseGate : BodyM (Var × Gate) := do
  let lhs ← parseDefiningLit
  let rhs0 ← skipSpace *> parseLit
  let rhs1 ← skipSpace *> parseLit
  return (lhs, { rhs0, rhs1 })

@[inline]
def parseGates : BodyM (Std.HashMap Var Gate) := do
  let n := (←getHeader).numAnds
  let mut gates := .emptyWithCapacity n
  for _ in [0:n] do
    let (var, gate) ← parseGate <* skipNewline
    let (contains, g) := gates.containsThenInsert var gate
    gates := g
    if contains then
      failM s!"gate {var.idx} defined multiple times"
  return gates

end ASCII

namespace Binary

@[inline]
partial def parseDelta (var : Nat := 0) (mul : Nat := 1) : Parser Nat := do
  let byte ← any
  let masked := byte &&& 0x7f

  -- We multiply by the shift rather than shift left because currently Lean's
  -- Nat shift left requires boxing the operands, even though in practice we
  -- rarely require this
  let var := var + masked.toNat * mul
  let mul := mul * 1 <<< 7

  match byte &&& 0x80 with
  | 0 => return var
  | _ => parseDelta var mul

-- Examples from the Aiger spec
/-- info: Except.ok 0 -/
#guard_msgs in
#eval! parseDelta.run [0x00].toByteArray

/-- info: Except.ok 127 -/
#guard_msgs in
#eval! parseDelta.run [0x7f].toByteArray

/-- info: Except.ok 128 -/
#guard_msgs in
#eval! parseDelta.run [0x80, 0x01].toByteArray

/-- info: Except.ok 258 -/
#guard_msgs in
#eval! parseDelta.run [0x82, 0x02].toByteArray

/-- info: Except.ok 16383 -/
#guard_msgs in
#eval! parseDelta.run [0xff, 0x7f].toByteArray

/-- info: Except.ok 16387 -/
#guard_msgs in
#eval! parseDelta.run [0x83, 0x80, 0x01].toByteArray

/-- info: Except.ok 268435455 -/
#guard_msgs in
#eval! parseDelta.run [0xff, 0xff, 0xff, 0x7f].toByteArray

/-- info: Except.ok 268435463 -/
#guard_msgs in
#eval! parseDelta.run [0x87, 0x80, 0x80, 0x80, 0x01].toByteArray

@[inline]
def parseGate (n : Nat) : BodyM (Var × Gate) := do
  let lhs := (←firstGate) + n
  let lhsLit := lhs.toLit
  let delta0 ← parseDelta
  let delta1 ← parseDelta

  if delta0 > lhsLit.idx then
    failM "rhs0 delta must be less than lhs"
  let rhs0 := .ofIdx (lhsLit.idx - delta0)

  if delta1 > rhs0.idx then
    failM "rhs1 delta must be less than rhs0"
  let rhs1 := .ofIdx (rhs0.idx - delta1)

  return (lhs, { rhs0, rhs1 })

@[inline]
def parseGates : BodyM (Std.HashMap Var Gate) := do
  let n := (←getHeader).numAnds
  let mut gates := .emptyWithCapacity n
  for i in [0:(←getHeader).numAnds] do
    let (var, gate) ← parseGate i
    gates := gates.insert var gate
  return gates

end Binary

public def parse (M : (Type -> Type)) [Monad M] [MonadLiftT Parser M] : M (Header × Aiger) := do
  let header ← parseHeader

  -- Run everything within a context where it can read the header
  (ReaderT.run · header) <| do

  if header.numFairness > 0 || header.numJustice > 0 then
    failM "justice and fairness properties not yet supported"

  if header.binary then
    if header.numInputs + header.numLatches + header.numAnds ≠ header.maxVar.idx then
      failM "number of inputs, latches and ands should sum to max var in binary aiger"

  let inputs ← parseInputs
  let latches ← parseLatches
  let outputs ← parseOutputLiterals header.numOutputs
  let bads ← parseOutputLiterals header.numBads
  let constraints ← parseOutputLiterals header.numConstraints
  -- TODO: Justice
  -- TODO: Fairness

  let gates ←
    if header.binary then
      Binary.parseGates
    else
      ASCII.parseGates

  let symbols ← parseSymbols
  let comments ← parseComments
  (eof : Parser _)

  return (header, { inputs, latches, outputs, bads, constraints, gates, symbols, comments })

end Parser
end Parser

@[inline]
public def parse (input : ByteArray) : Except String (Parser.Header × Parser.Aiger) :=
  Parser.parse Std.Internal.Parsec.ByteArray.Parser |>.run input

end Valaig.Aiger
