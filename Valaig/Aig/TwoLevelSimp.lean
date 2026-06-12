module

public import Valaig.Refs
import Std.Tactic.Do
import Std.Do

public section
namespace Valaig.Aig
namespace TwoLevelSimp

/-!
This module contains the two-level Aig simplification rules from "Local Two-Level And-Inverter Graph
Minimization without Blowup" by Brummayer and Biere.
-/

variable (assign : Lit -> Bool)
variable {assignInv : ∀ (lit : Lit), assign lit.invert = !assign lit}
variable {assignConst : ∀ inv, assign (.mk .constant inv) = inv}

inductive SimplifiedAnd where
| lit : Lit -> SimplifiedAnd
| and : Lit -> Lit -> SimplifiedAnd

namespace SimplifiedAnd

@[expose, simp, grind]
def denote (assign : Lit -> Bool) : SimplifiedAnd -> Bool
| lit l => assign l
| and l r => assign l && assign r

end SimplifiedAnd

-- Used for mvcgen proofs
open Std.Do
set_option mvcgen.warning false

@[inline]
def constFoldLeft (lhs rhs : Lit) : Option Lit := do
  if ¬lhs.isConstant then
    none

  -- Boundedness: (⊥ ∧ r) = ⊥
  if lhs = .false then
    return .false
  -- Neutrality: (⊤ ∧ r) = r
  else
    return rhs

include assignConst in
theorem denote_constFoldLeft {lhs rhs out : Lit} (heq : constFoldLeft lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  revert heq
  generalize h : constFoldLeft lhs rhs = res
  apply Option.of_wp_eq h
  unfold constFoldLeft
  mvcgen with (cbv; grind)

theorem var_constFoldLeft {lhs rhs out : Lit} (motive : Var -> Prop)
    (heq : constFoldLeft lhs rhs = some out)
    (hconst : motive .constant) (hrhs : motive rhs.var) :
    motive out.var := by
  revert heq
  generalize h : constFoldLeft lhs rhs = res
  apply Option.of_wp_eq h
  unfold constFoldLeft
  mvcgen with (cbv; grind)

@[inline]
def constFold (lhs rhs : Lit) : Option Lit := do
  if let some l := constFoldLeft lhs rhs then
    return l

  if let some l := constFoldLeft rhs lhs then
    return l

  none

include assignConst in
theorem denote_constFold {lhs rhs out : Lit} (heq : constFold lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  revert heq
  generalize h : constFold lhs rhs = res
  apply Option.of_wp_eq h
  unfold constFold
  mvcgen
  next heq => grind [denote_constFoldLeft assign (heq := heq)]
  next heq => grind [denote_constFoldLeft assign (heq := heq)]
  next => cbv; grind

theorem var_constFold {lhs rhs out : Lit} (motive : Var -> Prop)
    (heq : constFold lhs rhs = some out)
    (hconst : motive .constant) (hlhs : motive lhs.var) (hrhs : motive rhs.var) :
    motive out.var := by
  revert heq
  generalize h : constFold lhs rhs = res
  apply Option.of_wp_eq h
  unfold constFold
  mvcgen
  next heq => grind [var_constFoldLeft motive heq]
  next heq => grind [var_constFoldLeft motive heq]
  next => cbv; grind

@[inline]
def twoInput (lhs rhs : Lit) : Option Lit := do
  if let some l := constFold lhs rhs then
    return l

  -- Idempotence: (l ∧ l) = l
  if lhs = rhs then
    return lhs

  -- Contradiction: (l ∧ ¬l) = ⊥
  if lhs = rhs.invert then
    return .false

  none

include assignInv assignConst in
theorem denote_twoInput {lhs rhs out : Lit} (heq : twoInput lhs rhs = some out) :
    assign out = (assign lhs && assign rhs) := by
  revert heq
  generalize h : twoInput lhs rhs = res
  apply Option.of_wp_eq h
  unfold twoInput
  mvcgen
  next heq => grind [denote_constFold assign (heq := heq)]
  next heq => grind
  next heq => grind
  next => cbv; grind

theorem var_twoInput {lhs rhs out : Lit} (motive : Var -> Prop)
    (heq : twoInput lhs rhs = some out)
    (hconst : motive .constant) (hlhs : motive lhs.var) (hrhs : motive rhs.var) :
    motive out.var := by
  revert heq
  generalize h : twoInput lhs rhs = res
  apply Option.of_wp_eq h
  unfold twoInput
  mvcgen with (cbv; grind [var_constFold motive])

@[inline]
def threeInputLeftNeg (rhs l0 l1 : Lit) : Option SimplifiedAnd := do
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
  revert heq
  generalize h : threeInputLeftNeg rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeftNeg
  mvcgen with (cbv; grind)

theorem var_threeInputLeftNeg_lit {rhs l0 l1 out : Lit} (motive : Var -> Prop)
    (heq : threeInputLeftNeg rhs l0 l1 = some (.lit out))
    (hrhs : motive rhs.var) :
    motive out.var := by
  revert heq
  generalize h : threeInputLeftNeg rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeftNeg
  mvcgen with (cbv; grind)

theorem var_threeInputLeftNeg_and {rhs l0 l1 o0 o1 : Lit} (motive : Var -> Prop)
    (heq : threeInputLeftNeg rhs l0 l1 = some (.and o0 o1))
    (hl0 : motive l0.var) (hl1 : motive l1.var) :
    motive o0.var ∧ motive o1.var := by
  revert heq
  generalize h : threeInputLeftNeg rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeftNeg
  mvcgen with (cbv; grind)

@[inline]
def threeInputLeftPos (lhs rhs l0 l1 : Lit) : Option Lit := do
  -- Contradiction: (¬r ∧ l1) ∧ r = (l0 ∧ ¬r) ∧ r = ⊥
  if l0 = rhs.invert ∨ l1 = rhs.invert then
    return .false

  -- Idempotence: (l0 ∧ l1) ∧ l0 = (l0 ∧ l1) ∧ l1 = (l0 ∧ l1)
  if l0 = rhs ∨ l1 = rhs then
    return lhs

  none

include assignInv assignConst in
theorem denote_threeInputLeftPos {lhs rhs l0 l1 : Lit} {out : Lit}
    (heq : threeInputLeftPos lhs rhs l0 l1 = some out)
    (hl : assign lhs = (assign l0 && assign l1)) :
    assign out = (assign lhs && assign rhs) := by
  revert heq
  generalize h : threeInputLeftPos lhs rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeftPos
  mvcgen with (cbv; grind)

theorem var_threeInputLeftPos {lhs rhs l0 l1 out : Lit} (motive : Var -> Prop)
    (heq : threeInputLeftPos lhs rhs l0 l1 = some out)
    (hconst : motive .constant) (hlhs : motive lhs.var) :
    motive out.var := by
  revert heq
  generalize h : threeInputLeftPos lhs rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeftPos
  mvcgen with (cbv; grind)

@[inline]
def threeInputLeft (lhs rhs l0 l1 : Lit) : Option SimplifiedAnd := do
  if lhs.inverted then
    if let some l := threeInputLeftNeg rhs l0 l1 then
      return l
  else
    if let some l := threeInputLeftPos lhs rhs l0 l1 then
      return .lit l

  none

include assignInv assignConst in
theorem denote_threeInputLeft {lhs rhs l0 l1 : Lit} {out : SimplifiedAnd}
    (heq : threeInputLeft lhs rhs l0 l1 = some out)
    (hl : assign lhs = ((decide lhs.inverted) ^^ (assign l0 && assign l1))) :
    out.denote assign = (assign lhs && assign rhs) := by
  revert heq
  generalize h : threeInputLeft lhs rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeft
  mvcgen
  next heq => grind [denote_threeInputLeftNeg assign (heq := heq)]
  next => cbv; grind
  next h _ heq =>
    simp [h]at hl
    grind [denote_threeInputLeftPos assign (heq := heq)]
  next => cbv; grind

theorem var_threeInputLeft_lit {lhs rhs l0 l1 out : Lit} (motive : Var -> Prop)
    (heq : threeInputLeft lhs rhs l0 l1 = some (.lit out))
    (hconst : motive .constant) (hlhs : motive lhs.var) (hrhs : motive rhs.var) :
    motive out.var := by
  revert heq
  generalize h : threeInputLeft lhs rhs l0 l1 = res
  apply Option.of_wp_eq h
  unfold threeInputLeft
  mvcgen
  next heq => grind [var_threeInputLeftNeg_lit motive]
  next => cbv; grind
  next h _ heq => grind [var_threeInputLeftPos motive]
  next => cbv; grind

theorem var_threeInputLeft_and {lhs rhs l0 l1 o0 o1 : Lit} (motive : Var -> Prop)
    (heq : threeInputLeft lhs rhs l0 l1 = some (.and o0 o1))
    (hl0 : motive l0.var) (hl1 : motive l1.var) :
    motive o0.var ∧ motive o1.var := by
  grind [threeInputLeft, var_threeInputLeftNeg_and motive]

@[inline]
def fourInputPosPos (lhs l0 l1 r0 r1 : Lit) : Option SimplifiedAnd := do
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

include assignInv assignConst in
theorem denote_fourInputPosPos {lhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some out)
    (hl : assign lhs = (assign l0 && assign l1)) :
    out.denote assign = (assign lhs && (assign r0 && assign r1)) := by
  revert heq
  generalize h : fourInputPosPos lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosPos
  mvcgen with (cbv; grind)

theorem var_fourInputPosPos_lit {lhs l0 l1 r0 r1 out : Lit} (motive : Var -> Prop)
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some (.lit out))
    (hconst : motive .constant) :
    motive out.var := by
  revert heq
  generalize h : fourInputPosPos lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosPos
  mvcgen with (cbv; grind)

theorem var_fourInputPosPos_and {lhs l0 l1 r0 r1 o0 o1 : Lit} (motive : Var -> Prop)
    (heq : fourInputPosPos lhs l0 l1 r0 r1 = some (.and o0 o1))
    (hlhs : motive lhs.var) (hr0 : motive r0.var) (hr1 : motive r1.var) :
    motive o0.var ∧ motive o1.var := by
  revert heq
  generalize h : fourInputPosPos lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosPos
  mvcgen with (cbv; grind)

@[inline]
def fourInputPosNeg (lhs l0 l1 r0 r1 : Lit) : Option SimplifiedAnd := do
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
  revert heq
  generalize h : fourInputPosNeg lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosNeg
  mvcgen with (cbv; grind)

theorem var_fourInputPosNeg_lit {lhs l0 l1 r0 r1 out : Lit} (motive : Var -> Prop)
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some (.lit out))
    (hlhs : motive lhs.var) :
    motive out.var := by
  revert heq
  generalize h : fourInputPosNeg lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosNeg
  mvcgen with (cbv; grind)

theorem var_fourInputPosNeg_and {lhs l0 l1 r0 r1 o0 o1 : Lit} (motive : Var -> Prop)
    (heq : fourInputPosNeg lhs l0 l1 r0 r1 = some (.and o0 o1))
    (hlhs : motive lhs.var) (hr0 : motive r0.var) (hr1 : motive r1.var) :
    motive o0.var ∧ motive o1.var := by
  revert heq
  generalize h : fourInputPosNeg lhs l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputPosNeg
  mvcgen with (cbv; grind)

@[inline]
def fourInputNegNeg (l0 l1 r0 r1 : Lit) : Option Lit := do
  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(l0 ∧ ¬l1) = ¬l0
  if (l0 = r0 ∧ l1 = r1.invert) then
    return l0.invert

  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(¬l1 ∧ l0) = ¬l0
  if (l0 = r1 ∧ l1 = r0.invert) then
    return l0.invert

  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(l1 ∧ ¬l0) = ¬l1
  if (l1 = r0 ∧ l0 = r1.invert) then
    return l1.invert

  -- Resolution: ¬(l0 ∧ l1) ∧ ¬(¬l0 ∧ l1) = ¬l1
  if (l1 = r1 ∧ l0 = r0.invert) then
    return l1.invert

  none

include assignInv in
theorem denote_fourInputNegNeg {l0 l1 r0 r1 : Lit} {out : Lit}
    (heq : fourInputNegNeg l0 l1 r0 r1 = some out) :
    assign out = (!(assign l0 && assign l1) && !(assign r0 && assign r1)) := by
  revert heq
  generalize h : fourInputNegNeg l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputNegNeg
  mvcgen
  next h => simp only [Option.some.injEq]; intro h; cbv; grind only
  next h => simp only [Option.some.injEq]; intro h; cbv; grind only
  next h => simp only [Option.some.injEq]; intro h; cbv; grind only
  next h => simp only [Option.some.injEq]; intro h; cbv; grind only
  · cbv; grind


theorem var_fourInputNegNeg {l0 l1 r0 r1 out : Lit} (motive : Var -> Prop)
    (heq : fourInputNegNeg l0 l1 r0 r1 = some out)
    (hl0 : motive l0.var) (hl1 : motive l1.var) :
    motive out.var := by
  revert heq
  generalize h : fourInputNegNeg l0 l1 r0 r1 = res
  apply Option.of_wp_eq h
  unfold fourInputNegNeg
  mvcgen with (cbv; grind)

@[inline]
def fourInput (lhs rhs l0 l1 r0 r1 : Lit) : Option SimplifiedAnd :=
  match decide lhs.inverted, decide rhs.inverted with
  | false, false => fourInputPosPos lhs l0 l1 r0 r1
  | false,  true => fourInputPosNeg lhs l0 l1 r0 r1
  | true,  false => fourInputPosNeg rhs r0 r1 l0 l1
  | true,   true => fourInputNegNeg l0 l1 r0 r1 |>.map .lit

include assignInv assignConst in
theorem denote_fourInput {lhs rhs l0 l1 r0 r1 : Lit} {out : SimplifiedAnd}
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some out)
    (hl : assign lhs = ((decide lhs.inverted) ^^ (assign l0 && assign l1)))
    (hr : assign rhs = ((decide rhs.inverted) ^^ (assign r0 && assign r1))) :
    out.denote assign = (assign lhs && assign rhs) := by
  simp only [fourInput] at heq
  split at heq
  · rw [denote_fourInputPosPos assign heq (by simp_all)] <;> grind
  · rw [denote_fourInputPosNeg assign heq (by simp_all)] <;> grind
  · rw [denote_fourInputPosNeg assign heq (by simp_all)] <;> grind
  · simp only [Option.map_eq_some_iff] at heq
    rcases heq with ⟨res, ⟨heq, hlit⟩⟩
    simp only [SimplifiedAnd.denote]
    split
    · simp only [SimplifiedAnd.lit.injEq] at hlit
      rw [←hlit, denote_fourInputNegNeg assign heq]
      <;> grind
    · grind

theorem var_fourInput_lit {lhs rhs l0 l1 r0 r1 out : Lit} (motive : Var -> Prop)
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some (.lit out))
    (hconst : motive .constant)
    (hlhs : motive lhs.var) (hrhs : motive rhs.var)
    (hl0 : motive l0.var) (hl1 : motive l1.var) :
    motive out.var := by
  simp only [fourInput] at heq
  split at heq
  · grind [var_fourInputPosPos_lit motive]
  · grind [var_fourInputPosNeg_lit motive]
  · grind [var_fourInputPosNeg_lit motive]
  · grind [var_fourInputNegNeg motive, Option.map_eq_some_iff]


theorem var_fourInput_and {lhs rhs l0 l1 r0 r1 o0 o1 : Lit} (motive : Var -> Prop)
    (heq : fourInput lhs rhs l0 l1 r0 r1 = some (.and o0 o1))
    (hlhs : motive lhs.var) (hrhs : motive rhs.var)
    (hl0 : motive l0.var) (hl1 : motive l1.var)
    (hr0 : motive r0.var) (hr1 : motive r1.var) :
    motive o0.var ∧ motive o1.var := by
  simp only [fourInput] at heq
  split at heq
  · grind [var_fourInputPosPos_and motive]
  · grind [var_fourInputPosNeg_and motive]
  · grind [var_fourInputPosNeg_and motive]
  · grind [Option.map_eq_some_iff]

@[inline]
def simplifyAnd (lhs rhs : Lit) (lin rin : Option (Lit × Lit)) : SimplifiedAnd := Id.run do
  if let some lit := twoInput lhs rhs then
    return .lit lit

  if let some (l0, l1) := lin then
    if let some new := threeInputLeft lhs rhs l0 l1 then
      return new

  if let some (r0, r1) := rin then
    if let some new := threeInputLeft rhs lhs r0 r1 then
      return new

  if let some (l0, l1) := lin then
    if let some (r0, r1) := rin then
      if let some new := fourInput lhs rhs l0 l1 r0 r1 then
        return new

  return .and lhs rhs

include assignInv assignConst in
theorem denote_simplifyAnd {lhs rhs : Lit} {lin rin : Option (Lit × Lit)} {out : SimplifiedAnd}
    (heq : simplifyAnd lhs rhs lin rin = out)
    (hl : ∀ {l0 l1}, lin = some (l0, l1) → assign lhs = (lhs.inverted ^^ (assign l0 && assign l1)))
    (hr : ∀ {r0 r1}, rin = some (r0, r1) → assign rhs = (rhs.inverted ^^ (assign r0 && assign r1))) :
    out.denote assign = (assign lhs && assign rhs) := by
  have : .and lhs rhs = out → out.denote assign = (assign lhs && assign rhs) := by grind
  revert heq
  generalize h : simplifyAnd lhs rhs lin rin = res
  apply Id.of_wp_run_eq h
  mvcgen
  <;> (intro h; rw [←h])
  next heq => apply denote_twoInput assign heq <;> grind
  next heq => apply denote_threeInputLeft assign heq <;> grind
  next heq => rw [Bool.and_comm]; apply denote_threeInputLeft assign heq <;> grind
  next heq => apply denote_fourInput assign heq <;> grind
  next heq => apply denote_fourInput assign heq <;> grind
  next heq => rw [Bool.and_comm]; apply denote_threeInputLeft assign heq <;> grind
  next heq => apply denote_fourInput assign heq <;> grind
  next => grind

theorem var_simplifyAnd_lit {lhs rhs : Lit} {lin rin : Option (Lit × Lit)} {out : Lit} (motive : Var -> Prop)
    (heq : simplifyAnd lhs rhs lin rin = .lit out)
    (hconst : motive .constant) (hlhs : motive lhs.var) (hrhs : motive rhs.var)
    (hl : ∀ {l0 l1}, lin = some (l0, l1) → motive l0.var ∧ motive l1.var) :
    motive out.var := by
  revert heq
  generalize h : simplifyAnd lhs rhs lin rin = res
  apply Id.of_wp_run_eq h
  have {lhs rhs} : SimplifiedAnd.and lhs rhs = .lit out → motive out.var := by grind only
  mvcgen
  <;> (try apply this)
  <;> intro h
  next heq => simp only [SimplifiedAnd.lit.injEq] at h; rw [←h]; apply var_twoInput motive heq <;> grind
  next heq => rw [h] at heq; apply var_threeInputLeft_lit motive heq <;> grind
  next heq => rw [h] at heq; apply var_threeInputLeft_lit motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_lit motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_lit motive heq <;> grind
  next heq => rw [h] at heq; apply var_threeInputLeft_lit motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_lit motive heq <;> grind
  next => grind

theorem var_simplifyAnd_and {lhs rhs o0 o1 : Lit} {lin rin : Option (Lit × Lit)} (motive : Var -> Prop)
    (heq : simplifyAnd lhs rhs lin rin = .and o0 o1)
    (hlhs : motive lhs.var) (hrhs : motive rhs.var)
    (hl : ∀ {l0 l1}, lin = some (l0, l1) → motive l0.var ∧ motive l1.var)
    (hr : ∀ {r0 r1}, rin = some (r0, r1) → motive r0.var ∧ motive r1.var) :
    motive o0.var ∧ motive o1.var := by
  revert heq
  generalize h : simplifyAnd lhs rhs lin rin = res
  apply Id.of_wp_run_eq h
  have : SimplifiedAnd.and lhs rhs = .and o0 o1 → motive o0.var ∧ motive o1.var := by grind only
  mvcgen
  <;> (intro h; try simp at h)
  next heq => rw [h] at heq; apply var_threeInputLeft_and motive heq <;> grind
  next heq => rw [h] at heq; apply var_threeInputLeft_and motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_and motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_and motive heq <;> grind
  next heq => rw [h] at heq; apply var_threeInputLeft_and motive heq <;> grind
  next heq => rw [h] at heq; apply var_fourInput_and motive heq <;> grind
  next => grind

theorem var_simplifyAnd {lhs rhs : Lit} {lin rin : Option (Lit × Lit)} {out : SimplifiedAnd}
    (motive : Var -> Prop)
    (heq : simplifyAnd lhs rhs lin rin = out)
    (hconst : motive .constant := by grind) (hlhs : motive lhs.var := by grind) (hrhs : motive rhs.var := by grind)
    (hl : ∀ {l0 l1}, lin = some (l0, l1) → motive l0.var ∧ motive l1.var := by grind)
    (hr : ∀ {r0 r1}, rin = some (r0, r1) → motive r0.var ∧ motive r1.var := by grind) :
    match out with
    | .lit l => motive l.var
    | .and lhs rhs => motive lhs.var ∧ motive rhs.var := by
  split
  next heq => apply var_simplifyAnd_lit motive heq <;> trivial
  next heq => apply var_simplifyAnd_and motive heq <;> trivial

end TwoLevelSimp
end Valaig.Aig
