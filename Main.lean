import Valaig

abbrev MyState := Unit
abbrev MyParseT := StateT MyState

open Valaig Aig

-- open Valaig.Aig.Aiger.Parser

-- instance {m} [Monad m] : ActionsM (MyParseT m) where
--   addInput (var : Var) := do pure ()
--   addLatch (var : Var) (next : Lit) (reset : Option Lit) := do pure ()

--   addOutput (lit : Lit) := do pure ()
--   addBad (lit : Lit) := do pure ()
--   addConstraint (lit : Lit) := do pure ()

--   addGate (lhs : Var) (rhs0 rhs1 : Lit) := do pure ()

--   -- The indices of symbols correspond to the Nth call to the corresponding
--   -- add function
--   addSymbol (idx : Nat) (type : SymbolType) (symbol : String) := do pure ()
--   addComment (comment : String) := do pure ()


-- def main (args : List String) : IO Unit := do
--   match args with
--   | [path] =>
--     let contents ← IO.FS.readBinFile (.mk path)
--     let result := Valaig.Aiger.Parser.parse MyParseT |>.run () |>.run contents
--     match result with
--     | .ok (h, s) => IO.println s!"ok!"-- {repr h} {repr s}"
--     | .error e => IO.println s!"err: {e}"
--   | _ => IO.eprintln "<filename>"

def main (args : List String) : IO Unit := do
  let aig : Aig := .empty
  let (aig, i0) := aig.addInput
  let (aig, i1) := aig.addInput
  if h : ¬i0.validIn aig ∨ ¬i1.validIn aig then
    throw <| .userError "i0 or i1 bad!"
  else
    let (aig, conj) := aig.addGate i0 i1 (h0 := by omega) (h1 := by omega)
    let aig := aig.addBad conj

    if h : aig.numLatches > 0 then
      throw <| .userError "Has latches!"
    else
      let ric3 : Valaig.External.rIC3 := {}
      let res ← Valaig.External.checkSafety ric3 aig (hwf := by grind [Aig.WF])
      IO.println s!"Result: {repr res}"
