import Valaig

abbrev MyState := Unit
abbrev MyParseT := StateT MyState

open Valaig
open Valaig.Aig

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
  let aig : Std.Sat.AIG _ := .empty
  let inputs := #[]

  let res := aig.mkAtomCached (.input 0)
  let aig := res.aig
  let i0 := res.ref
  let inputs := inputs.push <| { var := Lit.ofRef res.ref |>.var }

  let res := aig.mkAtomCached (.input 1)
  let aig := res.aig
  let i1 := res.ref
  let inputs := inputs.push <| { var := Lit.ofRef res.ref |>.var }

  let res := aig.mkGateCached ⟨i1.flip true, i1⟩
  let aig := res.aig
  let bad := Lit.ofRef res.ref

  let aig : Aig := {
    aig,
    inputs,
    latches := #[],
    bads := #[{ lit := bad }],
    hfalse := sorry,
    hinputstodecl := sorry,
    hdecltoinputs := sorry,
    hlatchestodecl := sorry,
    hdecltolatches := sorry
  }

  let ric3 : Valaig.External.rIC3 := {}
  let res ← Valaig.External.checkSafety ric3 aig
  IO.println s!"Result: {repr res}"

