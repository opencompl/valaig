module

public import Valaig.Aig.Basic

public section
namespace Valaig.Aiger.Parser

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

structure Input where
  var : Var
deriving Repr, Inhabited

structure Latch where
  var : Var
  next : Lit
  reset : Option Lit
deriving Repr, Inhabited

structure Output where
  lit : Lit
deriving Repr, Inhabited

structure Gate where
  rhs0 : Lit
  rhs1 : Lit
deriving Repr, Inhabited

inductive SymbolType where
| input
| latch
| output
| bad
| constraint
| justice
| fairness
deriving Repr, Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev SymbolIndex := SymbolType × Nat
abbrev Symbol := SymbolIndex × String

/-
As the Std.Sat.AIG API makes it impossible to create an AIG with broken invariants, the parser
constructs a looser structure that just corresponds to the Aiger file first, from which the
legalised Aig is constructed.
-/
structure Aiger where
  header : Header
  inputs : Array Input
  latches : Array Latch
  outputs : Array Output
  bads : Array Output
  constraints : Array Output
  /-
  justice :
  fairness :
  -/
  gates : Std.HashMap Var Gate
  symbols : Std.HashMap SymbolIndex String
  comments : Array String
deriving Repr, Inhabited

