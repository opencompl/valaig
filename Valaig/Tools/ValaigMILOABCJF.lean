module

import Valaig.Aiger

public section

def main (args : List String) : IO Unit := do
  match args with
  | [fn] =>
    let file ← IO.FS.Handle.mk fn .read
    let contents ← file.readBinToEnd
    match Valaig.Aiger.parse contents with
    | .error msg => IO.eprintln s!"Error: {msg}"
    | .ok (header, aiger) =>
      let (constResets, undefinedResets) :=
        aiger.aig.latchesIter.fold (init := (0, 0)) fun counts latch =>
          match latch.getReset! aiger.aig with
          | some none         => (counts.fst, counts.snd + 1)
          | some (some reset) => if reset.isConstant then (counts.fst + 1, counts.snd) else counts
          | none              => counts
      let functionalResets := aiger.aig.numLatches - constResets - undefinedResets

      IO.println s!"M: {header.maxVar.idx}"
      IO.println s!"I: {aiger.aig.numInputs}"
      IO.println s!"L: {header.numLatches} (resets - const: {constResets}, x: {undefinedResets}, functional: {functionalResets})"
      IO.println s!"O: {aiger.outputs.size}"
      IO.println s!"A: {aiger.aig.numGates}"
      IO.println s!"B: {aiger.bads.size}"
      IO.println s!"C: {aiger.constraints.size}"
      IO.println s!"J: 0"
      IO.println s!"F: 0"
      IO.println s!"WellFormed: {decide aiger.aig.WF}"
    return ()
  | _ => IO.eprintln "Error: Expected exactly one filename argument"
