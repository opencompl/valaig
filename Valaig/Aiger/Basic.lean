import Std.Sat.AIG

open Std.Sat (AIG)

variable {α : Type} [Hashable α] [DecidableEq α]

namespace Valaig
namespace Aiger

/--
The definition of a latch in the aig.
-/
structure Latch (aig : AIG α) where
  next : aig.Ref
  reset : aig.Ref

abbrev Latch.Idx := Nat

/--
An atom in the combinational aig is either an input or a latch
-/
inductive Atom (α : Type) where
  | input : α → Atom α
  | latch : Latch.Idx → Atom α
deriving Hashable, DecidableEq

end Aiger

/--
An Aiger model checking problem.
-/
structure Aiger (α : Type) [Hashable α] [DecidableEq α] where
  aig : AIG (Aiger.Atom α)

  -- A mapping from latch indices (Atom.latch idx) to their definition
  latches : Array (Aiger.Latch aig)

  bad : aig.Ref

  -- TODO: invariants
  -- Latches indices should map to the corresponding atoms
  -- Resets should be stratified (non-cyclic) for executable semantics

namespace Aiger

/--
A timeframe in the execution of the model, starting from the initial state at 0
-/
abbrev Frame := Nat

structure Entrypoint (α : Type) [DecidableEq α] [Hashable α] where
  /--
  The Aiger that we are in.
  -/
  aiger : Aiger α
  /--
  The reference to the node in `aiger` that this `Entrypoint` targets.
  -/
  ref : AIG.Ref aiger.aig
  /--
  The timeframe that this `Entrypoint` targets.
  -/
  frame : Frame

def Entrypoint.toAIGEntrypoint (entry : Entrypoint α) : AIG.Entrypoint (Atom α) :=
  { aig := entry.aiger.aig, ref := entry.ref }

def denote (assign : α → Frame → Bool) (entry : Entrypoint α) : Bool :=
  sorry
--     AIG.denote assignAtFrame entry.toAIGEntrypoint
--   where
--     assignAtFrame (atom : Atom α) : Bool :=
--       match atom with
--       | .input a => assign a entry.frame
--       | .latch idx =>
--         let latch := entry.aiger.latches[idx]'(sorry)
--         match entry.frame with
--         | 0 => denote assign { entry with ref := latch.reset, frame := 0 }
--         | Nat.succ n =>  denote assign { entry with ref := latch.next, frame := n - 1 }

def safe (aiger : Aiger α) :=
  ∀ assign frame,
    denote assign { aiger, ref := aiger.bad, frame } = false

end Aiger
end Valaig
