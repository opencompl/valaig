import Valaig.Aiger.Parser

def main (args : List String) : IO Unit := do
  match args with
  | [fn] =>
    let file ← IO.FS.Handle.mk fn .read
    let contents ← file.readBinToEnd
    match Valaig.Aiger.parse contents with
    | .error msg => IO.eprintln s!"Error: {msg}"
    | .ok aiger =>
      IO.println "ok!"
      IO.println s!"header: {repr aiger.header}"
      IO.println s!"symbols: {repr aiger.symbols}"
      IO.println s!"comments: {repr aiger.comments}"
    return ()
  | _ => IO.eprintln "Error: Expected exactly one filename argument"
