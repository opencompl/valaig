import Valaig.Aig.Basic

namespace Valaig.Aig.Aiger

def writeAag (aig : Aig) (file : IO.FS.Stream) (hwf : aig.WF := by trivial) : IO Unit := do
  -- Aiger 1.9 Header M I L O A B C J F
  file.putStrLn s!"aag {aig.maxVar.idx} {aig.numInputs} {aig.numLatches} 0 {aig.numGates} {aig.numBads} 0 0 0"

  -- Input lines
  for input in aig.inputs do
    file.putStrLn s!"{input.var.toLit.idx}"

  -- Latch lines
  for h : latch in aig.latches do
    file.putStr s!"{latch.var.toLit.idx} {latch.next.get (hwf.hnext h) |>.idx}"
    if let some reset := latch.reset then
      file.putStr s!"{reset.idx}"
    file.putStrLn ""

  -- Bad lines
  for bad in aig.bads do
    file.putStrLn s!"{bad.lit.idx}"

  -- Gates
  for h : i in [0:aig.aig.decls.size] do
    if let .gate rhs0 rhs1 := aig.aig.decls[i] then
      let (rhs0, rhs1) := (Lit.ofFanin rhs0, Lit.ofFanin rhs1)
      let lhs := Var.ofIdx i |>.toLit
      file.putStrLn s!"{lhs.idx} {rhs0.idx} {rhs1.idx}"

  -- TODO: Symbols/comments
  file.flush

-- TODO: Binary writer

end Valaig.Aig.Aiger
