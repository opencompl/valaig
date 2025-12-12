import Valaig.Aiger.Basic

namespace Valaig.Aiger

variable {aig : Aiger} {var : Var}

@[grind .]
theorem validIn_ofAig {aig : Aig} (h : var.validIn aig) :
    var.validIn (ofAig aig) := by
  simp_all only [ofAig]

end Valaig.Aiger
