module

public import Valaig.Refs

public section
namespace Valaig.Aig
namespace TwoLevelSimp

/-!
This module contains the two-level Aig simplification rules from "Local Two-Level And-Inverter Graph
Minimization without Blowup" by Brummayer and Biere.
-/

variable (assign : Lit -> Bool)
variable {assignInv : ∀ lit, assign lit = (lit.inverted ^^ assign lit.strip)}
variable {assignFalse : assign .false = .false}

inductive SimplifiedAnd where
| lit : Lit -> SimplifiedAnd
| and : Lit -> Lit -> SimplifiedAnd

namespace SimplifiedAnd

@[expose, simp, grind]
def denote (assign : Lit -> Bool) : SimplifiedAnd -> Bool
| lit l => assign l
| and l r => assign l && assign r

end SimplifiedAnd

@[inline]
def constFoldLeft (lhs rhs : @&Lit) : Option Lit := do
  if ¬lhs.isConstant then
    none

  -- Boundedness: (⊥ ∧ r) = ⊥
  if lhs = .false then
    return false
  -- Neutrality: (⊤ ∧ r) = r
  else
    return rhs

include assignInv assignFalse in
theorem denote_constFoldLeft {lhs rhs out : Lit} (heq : constFoldLeft lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  grind [constFoldLeft]

@[grind →]
theorem values_constFoldLeft {lhs rhs out : Lit} (heq : constFoldLeft lhs rhs = some out) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var := by
  grind [constFoldLeft]

@[inline]
def constFold (lhs rhs : @&Lit) : Option Lit := do
  if let some l := constFoldLeft lhs rhs then
    return l

  if let some l := constFoldLeft rhs lhs then
    return l

  none

include assignInv assignFalse in
theorem denote_constFold {lhs rhs out : Lit} (heq : constFold lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  have := @denote_constFoldLeft assign
  grind [constFold]

@[grind →]
theorem values_constFold {lhs rhs out : Lit} (heq : constFold lhs rhs = some out) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var := by
  grind [constFold]

@[inline]
def twoInput (lhs rhs : @&Lit) : Option Lit := do
  if let some l := constFold lhs rhs then
    return l

  -- Idempotence: (l ∧ l) = l
  if lhs = rhs then
    return lhs

  -- Contradiction: (l ∧ ¬l) = ⊥
  if lhs = rhs.invert then
    return false

  none

include assignInv assignFalse in
theorem denote_twoInput {lhs rhs out : Lit} (heq : twoInput lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  have := @denote_constFold assign
  grind [twoInput]

@[grind →]
theorem values_twoInput {lhs rhs out : Lit} (heq : twoInput lhs rhs = some out) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var := by
  grind [twoInput]

@[inline]
def threeInputLeftNeg (rhs l0 l1 : @&Lit) : Option SimplifiedAnd := do
  -- Subsumption: ¬(¬r ∧ l1) ∧ r = ¬(l0 ∧ ¬r) ∧ r = r
  if l0 = rhs.invert ∨ l1 = rhs.invert then
    return .lit rhs

  -- Substitution: ¬(l0 ∧ r) ∧ r = (¬l0 ∧ r)
  if l1 = rhs then
    return .and l0.invert l1

  -- Substitution: ¬(r ∧ l1) ∧ r = (¬l1 ∧ r)
  if l0 = rhs then
    return .and l1.invert l0

  none

include assignInv in
theorem denote_threeInputLeftNeg {rhs l0 l1 : Lit} {out : SimplifiedAnd}
    (heq : threeInputLeftNeg rhs l0 l1 = some out) :
    out.denote assign = (!(assign l0 && assign l1) && assign rhs) := by
  simp [threeInputLeftNeg] at heq
  grind 

@[grind →]
theorem values_threeInputLeftNeg_lit {rhs l0 l1 out : Lit}
    (heq : threeInputLeftNeg rhs l0 l1 = some (.lit out)) :
    out.isConstant ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var := by
  grind [threeInputLeftNeg]

@[grind →]
theorem values_threeInputLeftNeg_and_lhs {rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeftNeg rhs l0 l1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var := by
  grind [threeInputLeftNeg]

@[grind →]
theorem values_threeInputLeftNeg_and_rhs {rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeftNeg rhs l0 l1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var := by
  grind [threeInputLeftNeg]

@[inline]
def threeInputLeftPos (lhs rhs l0 l1 : @&Lit) : Option SimplifiedAnd := do
  -- Contradiction: (¬r ∧ l1) ∧ r = (l0 ∧ ¬r) ∧ r = ⊥
  if l0 = rhs.invert ∨ l1 = rhs.invert then
    return .lit .false

  -- Idempotence: (l0 ∧ l1) ∧ l0 = (l0 ∧ l1) ∧ l1 = (l0 ∧ l1)
  if l0 = rhs ∨ l1 = rhs then
    return .lit lhs

  none

include assignInv assignFalse in
theorem denote_threeInputLeftPos {lhs rhs l0 l1 : Lit} {out : SimplifiedAnd}
    (heq : threeInputLeftPos lhs rhs l0 l1 = some out)
    (hl : assign lhs = (assign l0 && assign l1)) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp [threeInputLeftPos] at heq
  grind

@[grind →]
theorem values_threeInputLeftPos_lit {lhs rhs l0 l1 out : Lit}
    (heq : threeInputLeftPos lhs rhs l0 l1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var := by
  grind [threeInputLeftPos]

@[grind →]
theorem values_threeInputLeftPos_and_lhs {lhs rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeftPos lhs rhs l0 l1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var := by
  grind [threeInputLeftPos]

@[grind →]
theorem values_threeInputLeftPos_and_rhs {lhs rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeftPos lhs rhs l0 l1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var := by
  grind [threeInputLeftPos]

@[inline]
def threeInputLeft (lhs rhs l0 l1 : @&Lit) : Option SimplifiedAnd := do
  if lhs.inverted then
    if let some l := threeInputLeftNeg rhs l0 l1 then
      return l
  else
    if let some l := threeInputLeftPos lhs rhs l0 l1 then
      return l

  none

include assignInv assignFalse in
theorem denote_threeInputLeft {lhs rhs l0 l1 : Lit} {out : SimplifiedAnd}
    (heq : threeInputLeft lhs rhs l0 l1 = some out)
    (hl : assign lhs.strip = (assign l0 && assign l1)) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp [threeInputLeft] at heq
  split at heq
  · have := @denote_threeInputLeftNeg assign
    grind
  · have := @denote_threeInputLeftPos assign assignInv assignFalse lhs rhs l0 l1
    grind

@[grind →]
theorem values_threeInputLeft_lit {lhs rhs l0 l1 out : Lit}
    (heq : threeInputLeft lhs rhs l0 l1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var := by
  grind [threeInputLeft]

@[grind →]
theorem values_threeInputLeft_and_lhs {lhs rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeft lhs rhs l0 l1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var := by
  grind [threeInputLeft]

@[grind →]
theorem values_threeInputLeft_and_rhs {lhs rhs l0 l1 o0 o1 : Lit}
    (heq : threeInputLeft lhs rhs l0 l1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var := by
  grind [threeInputLeft]

@[inline]
def threeInput (lhs rhs l0 l1 r0 r1 : @&Lit) : Option SimplifiedAnd := do
  if let some l := threeInputLeft lhs rhs l0 l1 then
    return l

  if let some l := threeInputLeft rhs lhs r0 r1 then
    return l

  none

include assignInv assignFalse in
theorem denote_threeInput {lhs rhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : threeInput lhs rhs l0 l1 r0 r1 = some out)
    (hl : assign lhs.strip = (assign l0 && assign l1))
    (hr : assign rhs.strip = (assign r0 && assign r1)) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp [threeInput] at heq
  have := @denote_threeInputLeft assign
  grind

@[grind →]
theorem values_threeInput_lit {lhs rhs l0 l1 r0 r1 out : Lit}
    (heq : threeInput lhs rhs l0 l1 r0 r1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [threeInput]

@[grind →]
theorem values_threeInput_and_lhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : threeInput lhs rhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [threeInput]

@[grind →]
theorem values_threeInput_and_rhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : threeInput lhs rhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [threeInput]

@[inline]
def fourInputPosPos (lhs l0 l1 r0 r1 : @&Lit) : Option SimplifiedAnd := do
  -- Contradiction: (l0 ∧ l1) ∧ (¬l0 ∧ r1) = ⊥
  if l0 = r0.invert ∨ l0 = r1.invert ∨ l1 = r0.invert ∨ l1 = r1.invert then
    return .lit false

  -- We somewhat arbitrarily prefer keeping the lhs when doing idempotence. The further
  -- idempotence rules listed in the paper/abc are never triggered as these cover all cases

  -- Idempotence: (l0 ∧ l1) ∧ (l0 ∧ r1) = (l0 ∧ l1) ∧ (l1 ∧ r1) = (l0 ∧ l1) ∧ r1
  if l0 = r0 ∨ l1 = r0 then
    return .and lhs r1

  -- Idempotence: (l0 ∧ l1) ∧ (r0 ∧ l0) = (l0 ∧ l1) ∧ (l1 ∧ r1) = (l0 ∧ l1) ∧ r0
  if l0 = r1 ∨ l1 = r1 then
    return .and lhs r0

  none

include assignInv assignFalse in
theorem denote_fourInputPosPos {lhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some out)
    (hl : assign lhs = (assign l0 && assign l1)) :
    out.denote assign = (assign lhs && (assign r0 && assign r1)) := by
  simp [fourInputPosPos] at heq
  grind

@[grind →]
theorem values_fourInputPosPos_lit {lhs l0 l1 r0 r1 out : Lit}
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [fourInputPosPos]

@[grind →]
theorem values_fourInputPosPos_and_lhs {lhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [fourInputPosPos]

@[grind →]
theorem values_fourInputPosPos_and_rhs {lhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [fourInputPosPos]

@[inline]
def fourInputPosNeg (lhs l0 l1 r0 r1 : @&Lit) : Option SimplifiedAnd := do
  -- Subsumption: (l0 ∧ l1) ∧ ¬(¬l0 ∧ r1) = (l0 ∧ l1)
  if l0 = r0.invert ∨ l0 = r1.invert ∨ l1 = r0.invert ∨ l1 = r1.invert then
    return .lit lhs

  -- Substitution: (l0 ∧ l1) ∧ ¬(l0 ∧ r1) = (l0 ∧ l1) ∧ ¬r1
  if l0 = r0 ∨ l1 = r0 then
    return .and lhs r1.invert

  -- Substitution: (l0 ∧ l1) ∧ ¬(r0 ∧ l0) = (l0 ∧ l1) ∧ ¬r0
  if l0 = r1 ∨ l1 = r1 then
    return .and lhs r0.invert

  none

include assignInv in
theorem denote_fourInputPosNeg {lhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some out)
    (hl : assign lhs = (assign l0 && assign l1)) :
    out.denote assign = (assign lhs && !(assign r0 && assign r1)) := by
  simp [fourInputPosNeg] at heq
  grind

@[grind →]
theorem values_fourInputPosNeg_lit {lhs l0 l1 r0 r1 out : Lit}
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [fourInputPosNeg]

@[grind →]
theorem values_fourInputPosNeg_and_lhs {lhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [fourInputPosNeg]

@[grind →]
theorem values_fourInputPosNeg_and_rhs {lhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [fourInputPosNeg]

@[inline]
def fourInputNegNeg (l0 l1 r0 r1 : @&Lit) : Option SimplifiedAnd := do
  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(l0 ∧ ¬l1) = ¬l0
  if (l0 = r0 ∧ l1 = r1.invert) ∨ (l0 = r1 ∧ l1 = r0.invert) then
    return .lit l0.invert

  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(¬l0 ∧ l1) = ¬l1
  if (l1 = r0 ∧ l0 = r1.invert) ∨ (l1 = r1 ∧ l0 = r0.invert) then
    return .lit l1.invert

  none

include assignInv in
theorem denote_fourInputNegNeg {l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInputNegNeg l0 l1 r0 r1 = some out) :
    out.denote assign = (!(assign l0 && assign l1) && !(assign r0 && assign r1)) := by
  simp [fourInputNegNeg] at heq
  grind

@[grind →]
theorem values_fourInputNegNeg_lit {l0 l1 r0 r1 out : Lit}
    (heq : fourInputNegNeg l0 l1 r0 r1 = some (.lit out)) :
    out.isConstant ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [fourInputNegNeg]

@[grind →]
theorem values_fourInputNegNeg_and_lhs {l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputNegNeg l0 l1 r0 r1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [fourInputNegNeg]

@[grind →]
theorem values_fourInputNegNeg_and_rhs {l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInputNegNeg l0 l1 r0 r1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [fourInputNegNeg]

@[inline]
def fourInput (lhs rhs l0 l1 r0 r1 : @&Lit) : Option SimplifiedAnd :=
  match decide lhs.inverted, decide rhs.inverted with
  | false, false => fourInputPosPos lhs l0 l1 r0 r1
  | false,  true => fourInputPosNeg lhs l0 l1 r0 r1
  | true,  false => fourInputPosNeg rhs r0 r1 l0 l1
  | true,   true => fourInputNegNeg l0 l1 r0 r1

include assignInv assignFalse in
theorem denote_fourInput {lhs rhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some out)
    (hl : assign lhs.strip = (assign l0 && assign l1))
    (hr : assign rhs.strip = (assign r0 && assign r1)) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp [fourInput] at heq
  split at heq
  · have := @denote_fourInputPosPos assign
    grind
  · have := @denote_fourInputPosNeg assign
    grind
  · have := @denote_fourInputPosNeg assign
    grind
  · have := @denote_fourInputNegNeg assign
    grind

@[grind →]
theorem values_fourInput_lit {lhs rhs l0 l1 r0 r1 out : Lit}
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some (.lit out)) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [fourInput]

@[grind →]
theorem values_fourInput_and_lhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [fourInput]

@[grind →]
theorem values_fourInput_and_rhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some (.and o0 o1)) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [fourInput]

@[inline]
def simplifyAnd (lhs rhs l0 l1 r0 r1 : @&Lit) : SimplifiedAnd := Id.run do
  if let some l := twoInput lhs rhs then
    return .lit l

  if let some l := threeInput lhs rhs l0 l1 r0 r1 then
    return l

  if let some l := fourInput lhs rhs l0 l1 r0 r1 then
    return l
  
  return .and lhs rhs

include assignInv assignFalse in
theorem denote_simplifyAnd {lhs rhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : simplifyAnd lhs rhs l0 l1 r0 r1 = some out)
    (hl : assign lhs.strip = (assign l0 && assign l1))
    (hr : assign rhs.strip = (assign r0 && assign r1)) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp [simplifyAnd] at heq
  split at heq
  · have := @denote_twoInput assign
    grind
  · split at heq
    · have := @denote_threeInput assign
      grind
    · split at heq
      · have := @denote_fourInput assign
        grind
      · grind

@[grind →]
theorem values_simplifyAnd_lit {lhs rhs l0 l1 r0 r1 out : Lit}
    (heq : simplifyAnd lhs rhs l0 l1 r0 r1 = .lit out) :
    out.isConstant ∨ out.var = lhs.var ∨ out.var = rhs.var ∨ out.var = l0.var ∨ out.var = l1.var ∨ out.var = r0.var ∨ out.var = r1.var := by
  grind [simplifyAnd]

@[grind →]
theorem values_simplifyAnd_and_lhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : simplifyAnd lhs rhs l0 l1 r0 r1 = .and o0 o1) :
    o0.isConstant ∨ o0.var = lhs.var ∨ o0.var = rhs.var ∨ o0.var = l0.var ∨ o0.var = l1.var ∨ o0.var = r0.var ∨ o0.var = r1.var := by
  grind [simplifyAnd]

@[grind →]
theorem values_simplifyAnd_and_rhs {lhs rhs l0 l1 r0 r1 o0 o1 : Lit}
    (heq : simplifyAnd lhs rhs l0 l1 r0 r1 = .and o0 o1) :
    o1.isConstant ∨ o1.var = lhs.var ∨ o1.var = rhs.var ∨ o1.var = l0.var ∨ o1.var = l1.var ∨ o1.var = r0.var ∨ o1.var = r1.var := by
  grind [simplifyAnd]

end TwoLevelSimp
end Valaig.Aig
