import Valaig.Aiger
import Valaig.Cert

def main (args : List String) : IO Unit := do
  match args with
  | [model, cert] =>
    let model ← IO.FS.Handle.mk model .read
    let contents ← model.readBinToEnd
    match Valaig.Aiger.parse contents with
    | .error msg => IO.eprintln s!"Error: {msg}"
    | .ok (_, model) =>
      let cert ← IO.FS.Handle.mk cert .read
      let contents ← cert.readBinToEnd
      match Valaig.Aiger.parse contents with
      | .error msg => IO.eprintln s!"Error: {msg}"
      | .ok (_, cert) =>
        match Valaig.Cert.appendCert model cert with
        | .error msg => IO.eprintln s!"Error: {msg}"
        | .ok product =>
          product.writeAag (←IO.getStdout)
    return ()
  | _ => IO.eprintln "Error: Expected two filename arguments"
