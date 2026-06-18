module

public import Valaig.External.Aiger.Basic
import Valaig.Data.DetIter
import Std.Data.Iterators.Combinators.Zip
import Std.Data.Iterators.Producers.Repeat

public section
namespace Valaig.Aiger

attribute [local grind =] Array.mem_mergeSort

def writeAag (aiger : Aiger) (file : IO.FS.Stream) : IO Unit := do
  let aig := aiger.aig
  -- Aiger 1.9 Header M I L O A B C J F
  file.putStrLn s!"aag {aig.maxVar.idx} {aig.numInputs} {aig.numLatches} {aiger.outputs.size} {aig.numGates} {aiger.bads.size} {aiger.constraints.size} 0 0"

  -- TODO: handle gaps in the input indices
  -- Inputs
  for h : input in aig.inputsIter.toArray.mergeSort (·.idx < ·.idx) do
    file.putStrLn s!"{input.getLit aig |>.idx}"

  -- Latches
  for h : latch in aig.latchesIter.toArray.mergeSort (·.idx < ·.idx) do
    let lit := latch.getLit aig
    -- No reset is represented by setting the reset to this literal
    file.putStrLn s!"{lit.idx} {latch.getNext aig |>.idx} {latch.getReset aig |>.getD lit |>.idx}"

  -- Outputs/Bads/Constraints
  for output     in aiger.outputs     do file.putStrLn s!"{output.lit.idx}"
  for bad        in aiger.bads        do file.putStrLn s!"{bad.lit.idx}"
  for constraint in aiger.constraints do file.putStrLn s!"{constraint.lit.idx}"

  -- Gates
  for h : var in aig.iter do
    if let .and lhs rhs := aig[var]'(by simp_all) then
      file.putStrLn s!"{var.toLit.idx} {lhs.idx} {rhs.idx}"

  -- Leaf Symbols
  for (idx, symbol) in aiger.leafSymbols do
    match idx with
    | .input idx => file.putStrLn s!"i{idx.idx} {symbol}"
    | .latch idx => file.putStrLn s!"l{idx.idx} {symbol}"

  -- Output/Bad/Constraint symbols
  let printSymbols (arr : Array NamedLit) (c : Char) : IO Unit := do
    for (out, idx) in arr.iter.zip  (Std.Iter.repeat (· + 1) 0) do
      match out.name with
      | none => continue
      | some name => file.putStrLn s!"{c}{idx} {name}"

  printSymbols aiger.outputs 'o'
  printSymbols aiger.bads 'b'
  printSymbols aiger.constraints 'c'

  -- Comments
  for comment in aiger.comments do
    file.putStrLn comment

  file.flush

-- TODO: Binary writer

end Valaig.Aiger
