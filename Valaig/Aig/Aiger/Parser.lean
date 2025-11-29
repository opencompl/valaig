import Valaig.Aig.Basic
import Std.Internal.Parsec
import Std.Data.Iterators

namespace Valaig.Aig.Aiger.Parser

open Std.Internal.Parsec.ByteArray
open Std.Internal.Parsec

structure Header where
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
deriving Repr, Inhabited

inductive SymbolType where
| input : SymbolType
| latch : SymbolType
| output : SymbolType
| bad : SymbolType
| constraint : SymbolType
| justice : SymbolType
| fairness : SymbolType

abbrev HeaderT := ReaderT Header

class ActionsM (m : Type -> Type) where
  addInput (var : Var) : HeaderT m Unit
  addLatch (var : Var) (next : Lit) (reset : Option Lit) : HeaderT m Unit

  addOutput (lit : Lit) : HeaderT m Unit
  addBad (lit : Lit) : HeaderT m Unit
  addConstraint (lit : Lit) : HeaderT m Unit

  addGate (lhs : Var) (rhs0 rhs1 : Lit) : HeaderT m Unit

  -- The indices of symbols correspond to the Nth call to the corresponding
  -- add function
  addSymbol (idx : Nat) (type : SymbolType) (symbol : String) : HeaderT m Unit
  addComment (comment : String) : HeaderT m Unit

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

-- Open so we can call the functions without namespacing
open ActionsM

variable {α : Type} {m : Type -> Type}
variable [Monad m] [ActionsM m] [MonadLift Parser m]

@[inline]
def getHeader : HeaderT m Header :=
  read

@[inline]
def binary : HeaderT m Bool :=
  return (←getHeader).binary

namespace Binary

@[inline]
def firstInput : HeaderT m Var :=
  -- 0 is used for constant false
  return (Var.ofIdx 1)

@[inline]
def firstLatch : HeaderT m Var :=
  return (←firstInput).offset (←getHeader).numInputs

@[inline]
def firstGate : HeaderT m Var :=
  return (←firstLatch).offset (←getHeader).numLatches

end Binary

-- Lean can't automatically convert out of Parsec to our type so we use this
@[inline]
def failM (msg : String) : HeaderT m α :=
  (Std.Internal.Parsec.fail msg : Parser _)

@[inline]
def require {α : Type} (pred : α -> Bool) (error : String) (parse : HeaderT m α) : HeaderT m α := do
  let n ← parse
  if !(pred n) then
    failM error
  return n

@[inline]
def asLit (n : Nat) : HeaderT m Lit := do
  let lit := .ofIdx n
  if lit.var > (←getHeader).maxVar then
    failM "non-zero integer expected"
  return lit

-- Validates a literal used to define a gate/latch that must be even and non-zero
@[inline]
def asDefiningLit (n : Nat) : HeaderT m Var := do
  let lit ← asLit n
  if lit.isConstant then
    failM "non-zero integer literal expected"
  lit.defines.getDM <| failM "even integer literal expected"

@[inline]
def parseLit : HeaderT m Lit := parseNat >>= asLit

@[inline]
def parseDefiningLit : HeaderT m Var := parseNat >>= asDefiningLit

@[inline]
def parseNLines (parse : (idx : Nat) -> HeaderT m Unit) (n : Nat) : HeaderT m Unit := do
  for i in [0:n] do
    parse i <* skipNewline

@[inline]
def parseDefiningLiterals (action : Var -> HeaderT m Unit) (n : Nat) : HeaderT m Unit :=
  parseNLines (fun _ => parseDefiningLit >>= action) n

@[inline]
def parseOutputLiterals (action : Lit -> HeaderT m Unit) (n : Nat) : HeaderT m Unit :=
  parseNLines (fun _ => parseLit >>= action) n

@[inline]
def parseInputs : HeaderT m Unit := do
  let n := (←getHeader).numInputs
  if (←binary) then
    for i in [0:n] do
      addInput ((←Binary.firstInput).offset i)
  else
    parseDefiningLiterals addInput n

@[inline]
def parseLatch (n : Nat) : HeaderT m Unit := do
  let latch ←
    match ←binary with
    | true => pure <| (←Binary.firstLatch).offset n
    | false => parseDefiningLit <* skipSpace

  let next ← parseLit
  let reset ← (←tryParse (skipSpace *> parseNat)) |>.mapM asLit

  addLatch latch next reset

@[inline]
def parseLatches : HeaderT m Unit := do
  parseNLines parseLatch (←getHeader).numLatches

@[inline]
def parseSymbolLine : Parser (HeaderT m Unit) := do
  let type : SymbolType ←
    match ← (any : Parser _) <&> Char.ofUInt8 with
    | 'i' => pure SymbolType.input
    | 'l' => pure SymbolType.latch
    | 'o' => pure SymbolType.output
    | 'b' => pure SymbolType.bad
    | 'c' => pure SymbolType.constraint
    | 'j' => pure SymbolType.justice
    | 'f' => pure SymbolType.fairness
    | c => fail s!"Unsupported symbol type {c}"

  let idx ← parseNat
  let symb ←
    (attempt $ skipSpace *> takeUntil (. = '\n'.toUInt8)) <|>
    (pure ByteSlice.empty : Parser _)
  skipNewline

  match String.fromUTF8? symb.toByteArray with
  | none => fail "Couldn't decode non-UTF8 symbol"
  | some sym => pure (addSymbol idx type sym)

@[inline]
partial def parseSymbols : HeaderT m Unit := do
  if let some action ← tryParse parseSymbolLine then
    action
    parseSymbols

@[inline]
def parseCommentLine : Parser String := do
  let comment ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  match String.fromUTF8? comment.toByteArray with
  | none => fail "Couldn't decode non-UTF8 comment"
  | some c => return c

@[inline]
def parseCommentHeader : Parser Unit := do
  skipByteChar 'c'
  skipNewline

@[inline]
partial def parseComments : HeaderT m Unit :=
  attempt parseCommentHeader *> go
where
  go : HeaderT m Unit := do
    addComment (← attempt parseCommentLine)
    go

namespace ASCII

@[inline]
def parseGate : HeaderT m Unit := do
  let lhs ← parseDefiningLit
  let rhs0 ← skipSpace *> parseLit
  let rhs1 ← skipSpace *> parseLit
  addGate lhs rhs0 rhs1

@[inline]
def parseGates : HeaderT m Unit := do
  parseNLines (fun _ => parseGate) (←getHeader).numAnds

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
def parseGate (n : Nat) : HeaderT m Unit := do
  let lhs := (←firstGate).offset n
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
def parseGates : HeaderT m Unit := do
  for i in [0:(←getHeader).numAnds] do
    parseGate i

end Binary

def parse (mT : (Type -> Type) -> (Type -> Type))
    [ActionsM (mT Parser)] [Monad (mT Parser)] [MonadLift Parser (mT Parser)]
    : (mT Parser) Header := do
  let header ← parseHeader

  -- Run everything within a context where it can read the header
  (ReaderT.run · header) <| do

  if header.numFairness > 0 || header.numJustice > 0 then
    failM "Justice and Fairness properties not yet supported"

  if header.binary then
    if header.numInputs + header.numLatches + header.numAnds ≠ header.maxVar.idx then
      failM "number of inputs, latches and ands should sum to max var in binary aiger"

  parseInputs
  parseLatches
  parseOutputLiterals addOutput header.numOutputs
  parseOutputLiterals addBad header.numBads
  parseOutputLiterals addConstraint header.numConstraints
  -- TODO: Justice
  -- TODO: Fairness

  if header.binary then
    Binary.parseGates
  else
    ASCII.parseGates

  parseSymbols
  -- parseComments
  -- (eof : Parser _)

  return header

end Valaig.Aig.Aiger.Parser
