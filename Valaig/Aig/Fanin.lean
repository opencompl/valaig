module

public import Valaig.Aig.Core
public import Valaig.ForLean.Set

public section
namespace Valaig.Aig

variable {aig : Aig} {root var : Var} {reset : Bool}

/--
  Direct fan-in of a variable.
  This includes both inputs to and gates and reset variables for latches if `reset` is true.

  Note: This does not include the variable itself.
-/
inductive FI (aig : Aig) (root : Var) (reset : Bool := false) : Set Var where
| left  : aig[root]? = some (.and lhs rhs) -> aig.FI root reset lhs.var
| right : aig[root]? = some (.and lhs rhs) -> aig.FI root reset rhs.var
| reset : reset -> aig[root]? = some (.latch idx) -> idx.getReset? aig = some (some lit) -> aig.FI root reset lit.var

/--
  Reset fan-in of a variable.
  This includes both inputs to and gates and reset variables for latches.

  Note: This does not include the variable itself.
-/
@[simp, grind unfold]
abbrev RFI (aig : Aig) (root : Var) := aig.FI root true

/--
  Transistive fan-in of a variable.
  This is the transitive closure of `FI`, covering the combinational part of the Aig.

  Note: This does not include the variable itself.
-/
inductive TFI (aig : Aig) (root : Var) (reset : Bool := false) : Set Var where
| fanin : fanin ∈ aig.FI root reset -> aig.TFI root reset fanin
| trans : fanin ∈ aig.FI other reset -> other ∈ aig.TFI root reset -> aig.TFI root reset fanin

/--
  Reset transitive fan-in of a variable.

  Note: This does not include the variable itself.
-/
@[simp, grind unfold]
abbrev RTFI (aig : Aig) (root : Var) := aig.TFI root true

/--
  Stateful direct fan-in of a variable.
  This includes boths input to and gates, next state variables for latches and reset variables for
  latches if `reset` is true.

  Note: This does not include the variable itself.
-/
inductive SFI (aig : Aig) (root : Var) (reset : Bool := false) : Set Var where
| fanin : fanin ∈ aig.FI root reset -> aig.SFI root reset fanin
| next : aig[root]? = some (.latch idx) -> idx.getNext? aig = some next -> aig.SFI root reset next.var

/--
  Cone-of-influence.
  Any variable in the COI is transitively reachable through the inputs to and gates, next state
  functions of latches and reset functions of latches if `reset` is true.

  Note: This does not include the variable itself.
  Note: This can include false dependencies, as the next state function for all latches are
  included in this definition, even if they are only accessed through the reset state function
  of another latch.
-/
inductive COI (aig : Aig) (root : Var) (reset : Bool := true) : Set Var where
| fanin : fanin ∈ aig.SFI root reset -> aig.COI root reset fanin
| trans : fanin ∈ aig.SFI other reset -> other ∈ aig.COI root reset -> aig.COI root reset fanin

@[simp, grind unfold]
abbrev CCOI (aig : Aig) (root : Var) := aig.COI root false

attribute [local simp, local grind =] Set.mem_iff

/-
  FI.
-/

@[simp, grind =>]
theorem mem_fi_left (hand : aig[root]'valid = .and lhs rhs) :
    lhs.var ∈ aig.FI root reset := by
  grind [FI.left]

@[simp, grind =>]
theorem mem_fi_right (hand : aig[root]'valid = .and lhs rhs) :
    rhs.var ∈ aig.FI root reset := by
  grind [FI.right]

@[simp, grind →]
theorem mem_rfi_reset (hand : aig[root]'valid = .latch idx) (hreset : idx.getReset aig idxValid = some lit) :
    lit.var ∈ aig.RFI root := by
  grind [FI.reset]

@[simp, grind .]
theorem mem_rfi_of_mem_fi (mem : var ∈ aig.FI root reset) :
    var ∈ aig.RFI root := by
  induction mem <;> grind [FI]

@[simp, grind =>]
theorem mem_fi_of_mem_fi_false (mem : var ∈ aig.FI root false) :
    var ∈ aig.FI root reset := by
  cases reset <;> grind

/-
  TFI.
-/

@[simp, grind =>]
theorem mem_tfi_left (hand : aig[root]'valid = .and lhs rhs) :
    lhs.var ∈ aig.TFI root reset := by
  grind [TFI.fanin]

@[simp, grind =>]
theorem mem_tfi_right (hand : aig[root]'valid = .and lhs rhs) :
    rhs.var ∈ aig.TFI root reset := by
  grind [TFI.fanin]

@[simp, grind →]
theorem mem_rtfi_reset (hand : aig[root]'valid = .latch idx) (hreset : idx.getReset aig idxValid = some lit) :
    lit.var ∈ aig.RTFI root := by
  grind [TFI.fanin]

@[simp, grind .]
theorem mem_tfi_of_mem_fi (mem : var ∈ aig.FI root reset) :
    var ∈ aig.TFI root reset :=
  .fanin mem

@[simp, grind →]
theorem tfi_trans {a b c : Var} (hab : a ∈ aig.TFI b reset) (hbc : b ∈ aig.TFI c reset) :
    a ∈ aig.TFI c reset := by
  induction hab with
  | fanin hfi => exact .trans hfi hbc
  | trans hfi _ htfi => exact .trans hfi htfi

@[simp, grind →]
theorem tfi_trans_fi_left {a b c : Var} (hab : a ∈ aig.FI b reset) (hbc : b ∈ aig.TFI c reset) :
    a ∈ aig.TFI c reset :=
  tfi_trans (.fanin hab) hbc

@[simp, grind →]
theorem tfi_trans_fi_right {a b c : Var} (hab : a ∈ aig.TFI b reset) (hbc : b ∈ aig.FI c reset) :
    a ∈ aig.TFI c reset :=
  tfi_trans hab (.fanin hbc)

@[simp, grind .]
theorem mem_rtfi_of_mem_tfi (mem : var ∈ aig.TFI root reset) :
    var ∈ aig.RTFI root := by
  induction mem with
  | fanin => grind
  | trans _ _ hrtfi => grind [tfi_trans_fi_left ?_ hrtfi]

@[simp, grind =>]
theorem mem_tfi_of_mem_tfi_false (mem : var ∈ aig.TFI root false) :
    var ∈ aig.TFI root reset := by
  cases reset <;> grind

/-
  SFI.
-/


@[simp, grind .]
theorem mem_sfi_of_mem_fi (mem : var ∈ aig.FI root reset) :
    var ∈ aig.SFI root reset :=
  .fanin mem

@[simp, grind =>]
theorem mem_sfi_next (hand : aig[root]'valid = .latch idx) (hnext : idx.getNext aig idxValid = lit) :
    lit.var ∈ aig.SFI root reset := by
  grind [SFI.next]

@[simp, grind .]
theorem mem_reset_sfi_of_mem_sfi (mem : var ∈ aig.SFI root reset) :
    var ∈ aig.SFI root true := by
  induction mem <;> grind

@[simp, grind =>]
theorem mem_sfi_of_mem_sfi_false (mem : var ∈ aig.SFI root false) :
    var ∈ aig.SFI root reset := by
  cases reset <;> grind

/-
  COI.
-/

@[simp, grind =>]
theorem mem_coi_left (hand : aig[root]'valid = .and lhs rhs) :
    lhs.var ∈ aig.COI root reset := by
  grind [COI.fanin]

@[simp, grind =>]
theorem mem_coi_right (hand : aig[root]'valid = .and lhs rhs) :
    rhs.var ∈ aig.COI root reset := by
  grind [COI.fanin]

@[simp, grind →]
theorem mem_coi_reset (hand : aig[root]'valid = .latch idx) (hreset : idx.getReset aig idxValid = some lit) :
    lit.var ∈ aig.COI root := by
  grind [COI.fanin]

@[simp, grind =>]
theorem mem_coi_next (hand : aig[root]'valid = .latch idx) (hnext : idx.getNext aig idxValid = lit) :
    lit.var ∈ aig.COI root reset := by
  grind [COI.fanin]

@[simp, grind .]
theorem mem_coi_of_mem_sfi (mem : var ∈ aig.SFI root reset) :
    var ∈ aig.COI root reset :=
  .fanin mem

@[simp, grind .]
theorem mem_coi_of_mem_fi (mem : var ∈ aig.FI root reset) :
    var ∈ aig.COI root reset := by
  grind

@[simp, grind .]
theorem mem_coi_of_mem_tfi (mem : var ∈ aig.TFI root reset) :
    var ∈ aig.COI root reset := by
  induction mem with
  | fanin hfi => grind
  | trans _ _ hcoi => grind [COI.trans ?_ hcoi]

@[simp, grind →]
theorem coi_trans {a b c : Var} (hab : a ∈ aig.COI b reset) (hbc : b ∈ aig.COI c reset) :
    a ∈ aig.COI c reset := by
  induction hab with
  | fanin hfi => exact .trans hfi hbc
  | trans hfi _ hcoi => exact .trans hfi hcoi

@[simp, grind →]
theorem coi_trans_sfi_left {a b c : Var} (hab : a ∈ aig.SFI b reset) (hbc : b ∈ aig.COI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans (.fanin hab) hbc

@[simp, grind →]
theorem coi_trans_sfi_right {a b c : Var} (hab : a ∈ aig.COI b reset) (hbc : b ∈ aig.SFI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans hab (.fanin hbc)

@[simp, grind →]
theorem coi_trans_fi_left {a b c : Var} (hab : a ∈ aig.FI b reset) (hbc : b ∈ aig.COI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans (mem_coi_of_mem_fi hab) hbc

@[simp, grind →]
theorem coi_trans_fi_right {a b c : Var} (hab : a ∈ aig.COI b reset) (hbc : b ∈ aig.FI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans hab (mem_coi_of_mem_fi hbc)

@[simp, grind →]
theorem coi_trans_tfi_left {a b c : Var} (hab : a ∈ aig.TFI b reset) (hbc : b ∈ aig.COI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans (mem_coi_of_mem_tfi hab) hbc

@[simp, grind →]
theorem coi_trans_tfi_right {a b c : Var} (hab : a ∈ aig.COI b reset) (hbc : b ∈ aig.TFI c reset) :
    a ∈ aig.COI c reset :=
  coi_trans hab (mem_coi_of_mem_tfi hbc)

@[simp, grind .]
theorem mem_coi_of_mem_ccoi (mem : var ∈ aig.CCOI root) :
    var ∈ aig.COI root reset := by
  induction mem with
  | fanin hfi => grind
  | trans _ _ hcoi => grind [coi_trans_sfi_left ?_ hcoi]

@[simp, grind .]
theorem mem_coi_true_of_mem_coi (mem : var ∈ aig.COI root reset) :
    var ∈ aig.COI root true := by
  cases reset <;> grind

end Valaig.Aig

