module

public section
namespace Valaig

inductive Result where
| proof
| counterexample
deriving Hashable, DecidableEq, Repr, Inhabited

inductive Error where
| timeout (component : String) (timeMs : Nat)
| external (msg : String)
deriving Hashable, DecidableEq, Repr, Inhabited

instance : ToString Error where
  toString : Error -> String
  | .timeout component ms => s!"{component} timed out at {ms}ms"
  | .external msg => s!"external error: {msg}"

abbrev EResult := Except Error Result
abbrev VExcept := Except Error
