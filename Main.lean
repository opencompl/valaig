import Valaig

abbrev MyState := Unit
abbrev MyParseT := StateT MyState

open Valaig.Aig
open Valaig.Aiger.Parser

instance {m} [Monad m] : ActionsM (MyParseT m) where
  addInput (var : Var) := do pure ()
  addLatch (var : Var) (next : Lit) (reset : Option Lit) := do pure ()

  addOutput (lit : Lit) := do pure ()
  addBad (lit : Lit) := do pure ()
  addConstraint (lit : Lit) := do pure ()

  addGate (lhs : Var) (rhs0 rhs1 : Lit) := do pure ()

  -- The indices of symbols correspond to the Nth call to the corresponding
  -- add function
  addSymbol (idx : Nat) (type : SymbolType) (symbol : String) := do pure ()
  addComment (comment : String) := do pure ()


def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let contents ← IO.FS.readBinFile (.mk path)
    let result := Valaig.Aiger.Parser.parse MyParseT |>.run () |>.run contents
    match result with
    | .ok (h, s) => IO.println s!"ok!"-- {repr h} {repr s}"
    | .error e => IO.println s!"err: {e}"
  | _ => IO.eprintln "<filename>"
