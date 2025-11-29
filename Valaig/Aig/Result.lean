namespace Valaig.Aig

inductive Result where
| safe : Result
| unSafe : Result -- Weird capitalization because safe is a keyword...
| unknown : Result
deriving Hashable, DecidableEq, Repr, Inhabited

end Valaig.Aig
