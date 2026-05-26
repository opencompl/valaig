module

public import Valaig.Aig

public section
namespace Valaig

structure Aiger.NamedLit where
  lit : Lit
  name : Option String
deriving Inhabited, Repr

/--
  An `Aig` supplemented with the extra information present in an aiger file.
-/
structure Aiger where
  aig         : Aig
  leafSymbols : Std.HashMap Aig.LeafIdx String
  outputs     : Array Aiger.NamedLit
  bads        : Array Aiger.NamedLit
  constraints : Array Aiger.NamedLit
  comments    : Array String
deriving Inhabited, Repr

namespace Aiger

end Aiger
end Valaig
