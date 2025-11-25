import Valaig

abbrev MyState := Unit
abbrev MyParseT := StateT MyState

open Valaig.Aiger.Parser

instance : ActionsT MyParseT where
  addInput (var : Var) : ParserM MyParseT Unit := do pure ()
  addLatch (var : Var) (next : Lit) (reset : Option Lit) : ParserM MyParseT Unit := do pure ()

  addOutput (lit : Lit) : ParserM MyParseT Unit := do pure ()
  addBad (lit : Lit) : ParserM MyParseT Unit := do pure ()
  addConstraint (lit : Lit) : ParserM MyParseT Unit := do pure ()

  addGate (lhs : Var) (rhs0 rhs1 : Lit) : ParserM MyParseT Unit := do pure ()

  -- The indices of symbols correspond to the Nth call to the corresponding
  -- add function
  addSymbol (idx : Nat) (type : SymbolType) (symbol : String) : ParserM MyParseT Unit := do pure ()
  addComment (comment : String) : ParserM MyParseT Unit := do pure ()


def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    let contents ← IO.FS.readBinFile (.mk path)
    let result := Valaig.Aiger.Parser.parse MyParseT |>.run () |>.run contents
    match result with
    | .ok (h, s) => IO.println s!"ok!"-- {repr h} {repr s}"
    | .error e => IO.println s!"err: {e}"
  | _ => IO.eprintln "<filename>"
