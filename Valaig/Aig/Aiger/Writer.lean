import Valaig.Aig.Basic

namespace Valaig.Aig.Aiger.Writer

def writeAag (aig : Aig) (file : IO.FS.Stream) : IO Unit := do
  -- Aiger 1.9 Header M I L O A B C J F
  file.putStrLn s!"aag {aig.maxVar.idx} {aig.numInputs} {aig.numLatches} 0 {aig.numGates} {aig.numBads} 0 0 0"

  -- Input lines
  for input in aig.inputs do
    file.putStrLn s!"{input.var.toLit.idx}"

  -- Latch lines
  for latch in aig.latches do
    file.putStrLn s!"{latch.var.toLit.idx} {latch.next.idx} {latch.reset.idx}"

  -- Bad lines
  for bad in aig.bads do
    file.putStrLn s!"{bad.lit.idx}"

  -- Gates
  for h : i in [0:aig.aig.decls.size] do
    if let .gate rhs0 rhs1 := aig.aig.decls[i] then
      let (rhs0, rhs1) : Lit × Lit := (rhs0, rhs1)
      let lhs := Var.ofIdx i |>.toLit
      file.putStrLn s!"{lhs.idx} {rhs0.idx} {rhs1.idx}"

  -- TODO: Symbols/comments

-- TODO: Binary writer

end Valaig.Aig.Aiger.Writer
