namespace Valaig.Aig

inductive Result where
| proof : Result
| counterexample : Result
| unknown : Result
deriving Hashable, DecidableEq, Repr, Inhabited

end Valaig.Aig
