namespace Valaig

inductive Result where
| proof : Result
| counterexample : Result
deriving Hashable, DecidableEq, Repr, Inhabited

inductive Error where
| timeout (component : String) (timeMs : Nat) : Error
| external (msg : String) : Error
deriving Hashable, DecidableEq, Repr, Inhabited

abbrev EResult := Except Error Result
abbrev VExcept := Except Error

end Valaig
