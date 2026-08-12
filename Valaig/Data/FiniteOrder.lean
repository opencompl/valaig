module

public section
namespace Valaig.Data

class FinitePartialOrder {α : Type u} (lt : α -> α -> Prop) where
  -- The relation is a partial order
  irrefl a : ¬lt a a
  trans a b c : lt a b → lt b c → lt a c

  -- We show finiteness by always being able to enumerate a set of values
  list : α -> List α
  nodup a : (list a).Nodup
  mem_list a b : a ∈ list b ↔ lt a b

attribute [simp, grind .] FinitePartialOrder.nodup
attribute [simp, grind =] FinitePartialOrder.mem_list

namespace FinitePartialOrder

variable {α : Type u} {lt : α -> α -> Prop}

@[expose, implicit_reducible, simp, grind]
def le (_fin : FinitePartialOrder lt) : α -> α -> Prop :=
  fun a b => a = b ∨ lt a b

@[expose, implicit_reducible, simp, grind]
def le_list (fin : FinitePartialOrder lt) (a : α) : List α :=
  a :: (fin.list a)

@[expose, implicit_reducible]
def measure (fin : FinitePartialOrder lt) (a : α) : Nat :=
  (fin.list a).length

variable [fin : FinitePartialOrder lt] {a b : α}

@[simp, grind .]
theorem nodup_le_list :
    (fin.le_list a).Nodup := by
  grind [fin.irrefl]

@[simp, grind =]
theorem mem_le_list_iff :
    a ∈ fin.le_list b ↔ fin.le a b := by
  simp

@[simp, grind .]
theorem le_refl :
    fin.le a a := by
  simp

theorem lt_asymm :
    lt a b → ¬lt b a := by
  grind [fin.irrefl, fin.trans]

@[simp, grind .]
theorem le_trans {c : α} (hab : fin.le a b) (hbc : fin.le b c) :
    fin.le a c := by
  grind [fin.trans]

@[simp, grind .]
theorem measure_le (h : fin.le a b) :
    fin.measure a ≤ fin.measure b := by
  apply List.Nodup.length_le_of_subset
  · apply nodup
  · grind [fin.trans, fin.mem_list]

@[simp, grind .]
theorem measure_lt (h : lt a b) :
    fin.measure a < fin.measure b := by
  classical
  simp only [measure]
  generalize ha : fin.list a = la
  generalize hb : fin.list b = lb
  suffices la.length < lb.length by grind
  have : a ∈ lb := by grind
  have : a ∉ la := by grind [fin.irrefl]
  have : ∀ c ∈ la, c ∈ lb := by grind [fin.trans]
  have : la.Nodup := by grind
  clear ha hb
  induction h : la generalizing lb la with
  | nil => grind
  | cons head tail ih => grind [ih tail (lb.erase head)]

end FinitePartialOrder

instance : @FinitePartialOrder Nat (· < ·) where
  irrefl := by omega
  trans := by omega

  list := (.range ·)
  nodup := by grind
  mem_list := by grind

instance {α : Type _} {rel : α -> α -> Prop} {p : α -> Prop} [DecidablePred p] [fin : FinitePartialOrder rel] :
    @FinitePartialOrder (Subtype p) (rel ·.val ·.val) where
  irrefl := by intros; apply fin.irrefl
  trans := by intro a b c; apply fin.trans

  list x := fin.list x.val |>.filter p |>.attachWith _ (by grind)
  nodup := sorry
  mem_list := by grind

end Valaig.Data
