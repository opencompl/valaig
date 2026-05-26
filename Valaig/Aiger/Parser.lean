module

public import Valaig.Aiger.Basic
public import Std.Internal.Parsec
public meta import Std.Internal.Parsec

namespace Valaig.Aiger.Parser

public structure Header where
  binary : Bool
  maxVar : Var
  numInputs : Nat
  numLatches : Nat
  numOutputs : Nat
  numAnds : Nat
  numBads : Nat
  numConstraints : Nat
  numJustice : Nat
  numFairness : Nat
deriving Inhabited, Repr

open Std.Internal.Parsec.ByteArray
open Std.Internal.Parsec
open Aig

section Parser

/--
  Construct the default aig for the parser as an aig with `maxVar` variable initialized, each
  constructed as an and gate with `maxVar` as inputs. This stands as a placeholder.
-/
def Header.defaultAiger (header : Header) : Aiger :=
  let aig := Aig.empty
  let lit := header.maxVar + 1 |>.toLit
  let aig := header.maxVar.idx.fold (init := aig) fun _ _ aig =>
    aig.addAnd lit lit |>.fst
  let default : Aiger := Inhabited.default
  { default with aig }

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

variable {BodyM : Type -> Type} [Monad BodyM] [MonadLiftT Parser BodyM] [MonadReaderOf Header BodyM]
variable [MonadExcept String BodyM] [MonadStateOf Aiger BodyM]
variable {α : Type}

def modifyAig (f : Aig -> Option Aig) : BodyM Unit := do
  modifyThe Aiger fun aiger =>
    { aiger with aig := (f aiger.aig).get! }

@[inline]
def addInput (idx : InputIdx) (var : Var) : BodyM Unit :=
  modifyAig <| fun aig => do
    let (aig, fresh) ← aig.convertAndToInput! var
    fresh.changeIdx! idx aig

@[inline]
def addLatch (idx : LatchIdx) (var : Var) (next : Lit) (reset : Option Lit) : BodyM Unit :=
  modifyAig <| fun aig => do
    let (aig, fresh) ← aig.convertAndToLatch! var next reset
    fresh.changeIdx! idx aig

@[inline]
def addGate (var : Var) (rhs0 rhs1 : Lit) : BodyM Unit :=
  modifyAig <| fun aig =>
    aig.rewriteAnd! var rhs0 rhs1

-- Lean can't automatically convert out of Parsec to our type so we use this
@[inline]
def failM (msg : String) : BodyM α :=
  (Std.Internal.Parsec.fail msg : Parser _)

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
def parseNLines (n : Nat) (parse : (idx : Nat) -> BodyM Unit) : BodyM Unit := do
  for i in [0:n] do
    parse i <* skipNewline

@[inline]
def parseNLinesToArray {α : Type} (n : Nat) (parse : (idx : Nat) -> BodyM α) : BodyM (Array α) := do
  let mut arr := .emptyWithCapacity n
  for i in [0:n] do
    arr := arr.push (← parse i <* skipNewline)
  return arr

@[inline]
def parseInputs : BodyM Unit := do
  let n := (←getHeader).numInputs

  if (←binary) then
    let first ← Binary.firstInput
    for idx in [0:n] do
      addInput (.ofIdx idx) (first + idx)
  else
    parseNLines n fun idx => do
      addInput (.ofIdx idx) (←parseDefiningLit)

@[inline]
def parseLatch (idx : Nat) : BodyM Unit := do
  let var ←
    match ←binary with
    | true => pure <| (←Binary.firstLatch) + idx
    | false => parseDefiningLit <* skipSpace

  let next ← parseLit
  let reset ← (←tryParse (skipSpace *> parseNat)) |>.mapM asLit
  let reset := if reset = some var then none else reset.getD .false

  addLatch (.ofIdx idx) var next reset

@[inline]
def parseLatches : BodyM Unit := do
  parseNLines (←getHeader).numLatches parseLatch

@[inline]
def parseOutputLiterals (n : Nat) : BodyM (Array NamedLit) :=
  parseNLinesToArray n <| fun _ => do return NamedLit.mk (←parseLit) none

@[inline]
def parseSymbolLine : BodyM (Char × Nat × String) := do
  let type ← (any : Parser _) <&> Char.ofUInt8

  let idx ← parseNat
  let symb ←
    (attempt $ skipSpace *> takeUntil (. = '\n'.toUInt8)) <|>
    (pure ByteSlice.empty : Parser _)
  skipNewline

  match String.fromUTF8? symb.toByteArray with
  | none     => failM "couldn't decode non-UTF8 symbol"
  | some sym => return (type, idx, sym)


@[inline]
partial def parseSymbols : BodyM Unit := do
  repeat
    match ← tryParse parseSymbolLine with
    | some ('i', idx, s) => modifyThe Aiger fun aiger => { aiger with leafSymbols := aiger.leafSymbols.insert (InputIdx.ofIdx idx) s }
    | some ('l', idx, s) => modifyThe Aiger fun aiger => { aiger with leafSymbols := aiger.leafSymbols.insert (LatchIdx.ofIdx idx) s }
    | some ('o', idx, s) => modifyThe Aiger fun aiger => { aiger with outputs     := aiger.outputs.modify idx ({ · with name := s }) }
    | some ('b', idx, s) => modifyThe Aiger fun aiger => { aiger with bads        := aiger.bads.modify idx ({ · with name := s }) }
    | some ('c', idx, s) => modifyThe Aiger fun aiger => { aiger with constraints := aiger.constraints.modify idx ({ · with name := s }) }
    -- | 'j' =>
    -- | 'f' =>
    | some c => failM s!"unsupported symbol type {c}"
    | none => break

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
def parseGate : BodyM Unit := do
  let lhs ← parseDefiningLit
  let rhs0 ← skipSpace *> parseLit
  let rhs1 ← skipSpace *> parseLit
  addGate lhs rhs0 rhs1

@[inline]
def parseGates : BodyM Unit := do
  parseNLines (←getHeader).numAnds fun _ => parseGate

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
def parseGate (n : Nat) : BodyM Unit := do
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

  addGate lhs rhs0 rhs1

@[inline]
def parseGates : BodyM Unit := do
  for i in [0:(←getHeader).numAnds] do
    parseGate i

end Binary

public def parse (M : (Type -> Type)) [Monad M] [MonadLiftT Parser M] : M (Header × Aiger) := do
  let header ← parseHeader

  -- Run everything within a context where it can read the header
  (ReaderT.run · header) <| do

  -- Create a default aiger to modify as we parse
  (StateT.run · header.defaultAiger) <| do

  if header.numFairness > 0 || header.numJustice > 0 then
    failM "justice and fairness properties not yet supported"

  if header.binary then
    if header.numInputs + header.numLatches + header.numAnds ≠ header.maxVar.idx then
      failM "number of inputs, latches and ands should sum to max var in binary aiger"

  parseInputs
  parseLatches
  let outputs ← parseOutputLiterals header.numOutputs
  let bads ← parseOutputLiterals header.numBads
  let constraints ← parseOutputLiterals header.numConstraints
  modifyThe Aiger fun aiger => { aiger with outputs, bads, constraints }
  -- TODO: Justice
  -- TODO: Fairness

  if header.binary then
    Binary.parseGates
  else
    ASCII.parseGates

  parseSymbols
  let comments ← parseComments
  modifyThe Aiger fun aiger => { aiger with comments }
  (eof : Parser _)

  return header

end Parser
end Parser

@[inline]
public def parse (input : ByteArray) : Except String (Parser.Header × Aiger) :=
  Parser.parse Std.Internal.Parsec.ByteArray.Parser |>.run input

end Valaig.Aiger
