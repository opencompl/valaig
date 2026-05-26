import Valaig.Aiger.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [fn] =>
    let file ← IO.FS.Handle.mk fn .read
    let contents ← file.readBinToEnd
    match Valaig.Aiger.parse contents with
    | .error msg => IO.eprintln s!"Error: {msg}"
    | .ok (header, aiger) =>
      let wf : Bool := aiger.aig.WF
      IO.println "ok!"
      IO.println s!"header: {repr header}"
      IO.println s!"comments: {repr aiger.comments}"
      IO.println s!"wf : {wf}"
    return ()
  | _ => IO.eprintln "Error: Expected exactly one filename argument"
