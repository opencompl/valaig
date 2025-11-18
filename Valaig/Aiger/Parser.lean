import Valaig.Aiger.Basic
import Std.Internal.Parsec
import Std.Data.Iterators

namespace Valaig
namespace Aiger.Parser

open Std.Internal.Parsec.ByteArray
open Std.Internal.Parsec

@[inline, specialize parse]
private def require {α : Type} (parse : Parser α) (pred : α → Bool) (error : String) : Parser α := do
  let n ← parse
  if !(pred n) then
    fail error
  return n

@[inline, specialize parse]
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
  return ⟨header, binary⟩

namespace ASCII

@[inline]
def parseVariable : Parser Nat := parseNat

@[inline]
def parsePos : Parser Nat :=
  require parseNat (. > 0) "non-zero integer expected"

@[inline]
def parseLiteral : Parser Nat :=
  require parsePos (. &&& 1 = 0) "even integer literal expected"

@[inline, specialize parse]
def parseNLines {α : Type} (parse : Parser α) (n : Nat) : Parser (Array α) := do
  let mut lines := .emptyWithCapacity n
  for _ in [0:n] do
    lines := lines.push (← parse <* skipNewline)
  return lines

@[inline]
def parseLatch : Parser Unit := do
  let latch ← parseLiteral
  let next ← skipSpace *> parseVariable
  let reset ← tryParse (skipSpace *> parseVariable)

  let _ := latch
  let _ := next
  let _ := reset
  pure ()

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
def parseSymbolLine : Parser Unit := do
  let type ← satisfy ("ilobcjf".contains $ Char.ofUInt8 .)
  let pos ← parseNat
  skipSpace
  let symb ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  let _ := type
  let _ := pos
  let _ := symb
  pure ()

@[inline]
def parseCommentLine : Parser Unit := do
  let comment ← takeUntil (. = '\n'.toUInt8)
  skipNewline
  let _ := comment
  pure ()

@[inline]
def parseCommentHeader : Parser Unit := do
  skipByteChar 'c'
  skipNewline

def parseBody (header : Header) : Parser Unit := do
  let inputs ← parseNLines parseLiteral header.numInputs
  let latches ← parseNLines parseLatch header.numLatches
  let outputs ← parseNLines parseVariable header.numOutputs
  let bads ← parseNLines parseVariable header.numBads
  let constraints ← parseNLines parseVariable header.numConstraints
  let gates ← parseNLines parseGate header.numAnds
  let symbols ← many parseSymbolLine
  let comments ← attempt (parseCommentHeader *> many parseCommentLine) <|> pure #[]
  eof

end ASCII

namespace Binary



end Binary

def parse : Parser Unit := do
  let ⟨header, binary⟩ ← parseHeader
  if header.numFairness > 0 || header.numJustice > 0 then
    fail "Justice and Fairness properties not yet supported"

  if binary then
    fail "binary aig format not yet supported"
  else
    ASCII.parseBody header

end Aiger.Parser
end Valaig
