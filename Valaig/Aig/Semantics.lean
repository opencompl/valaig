module

import all Valaig.Aig.Basic
public import Valaig.Aig.WellFormed

public section
namespace Valaig.Aig

abbrev Frame := Nat

@[expose]
def denote (aig : Aig) (lit : Lit) (frame : Frame) (input : InputIdx.In aig -> Frame -> Bool)
    (valid : lit.validIn aig := by grind) (wf : aig.WellFormed := by grind) : Bool :=
  let val :=
    match h : aig[lit.var] with
    | .false => false
    | .input idx => input ⟨idx, by grind⟩ frame
    | .latch idx =>
      if h0 : frame = 0 then
        aig.denote (idx.getReset aig) 0 input
      else
        aig.denote (idx.getNext aig) (frame - 1) input
    | .and rhs0 rhs1 =>
      let v0 := aig.denote rhs0 frame input
      let v1 := aig.denote rhs1 frame input
      v0 && v1

  val ^^ lit.inverted

termination_by (frame, lit.var)
decreasing_by all_goals grind
