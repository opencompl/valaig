module

public import Valaig.Aiger.Basic
import all Valaig.Aig.Basic
public import Valaig.Aig.Iter

public section
namespace Valaig.Aiger

def writeAag (aiger : Aiger) (file : IO.FS.Stream) : IO Unit := do
  let aig := aiger.aig
  -- Aiger 1.9 Header M I L O A B C J F
  file.putStrLn s!"aag {aig.maxVar.idx} {aig.numInputs} {aig.numLatches} 0 {aig.numGates} {aiger.numBads} 0 0 0"

  -- Input lines
  for h : input in aig.inputIter do
    file.putStrLn s!"{input.getLit aig |>.idx}"

  -- Latch lines
  for h : latch in aig.latchIter do
    file.putStrLn s!"{latch.getLit aig |>.idx} {latch.getNext aig |>.idx} {latch.getReset aig |>.idx}"

  -- Bad lines
  for bad in aiger.bads do
    file.putStrLn s!"{bad.lit.idx}"

  -- Gates
  for h : var in aig.iter do
    if let .and rhs0 rhs1 := aig[var] then
      file.putStrLn s!"{var.toLit.idx} {rhs0.idx} {rhs1.idx}"

  -- TODO: Symbols/comments
  file.flush

-- TODO: Binary writer

end Valaig.Aiger
