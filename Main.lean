import Valaig

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let contents ← IO.FS.readBinFile (.mk path)
    match Valaig.Aiger.Parser.parse.run contents with
    | .ok _ => IO.println "ok!"
    | .error e => IO.println s!"err: {e}"
  | _ => IO.eprintln "<filename>"
