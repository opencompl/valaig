import Valaig.Aiger.Basic

namespace Valaig.Aiger

def writeAag (aiger : Aiger) (file : IO.FS.Stream) : IO Unit := do
  let aig := aiger.aig
  -- Aiger 1.9 Header M I L O A B C J F
  file.putStrLn s!"aag {aig.maxVar.idx} {aig.numInputs} {aig.numLatches} 0 {aig.numGates} {aiger.numBads} 0 0 0"

  -- Input lines
  for input in aig.inputs do
    file.putStrLn s!"{input.var.toLit.idx}"

  -- Latch lines
  for h : latch in aig.latches do
    file.putStrLn s!"{latch.lit.idx} {latch.next.idx} {latch.reset.idx}"

  -- Bad lines
  for bad in aiger.bads do
    file.putStrLn s!"{bad.lit.idx}"

  -- Gates
  for h : i in [0:aig.size] do
    if let .gate rhs0 rhs1 := aig.aig.decls[i] then
      let (rhs0, rhs1) := (Lit.ofFanin rhs0, Lit.ofFanin rhs1)
      let lhs := Var.ofIdx i |>.toLit
      file.putStrLn s!"{lhs.idx} {rhs0.idx} {rhs1.idx}"

  -- TODO: Symbols/comments
  file.flush

-- TODO: Binary writer

end Valaig.Aiger
