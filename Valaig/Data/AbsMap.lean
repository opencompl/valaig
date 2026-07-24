module

public import Valaig.ForLean.Prelude
public import Valaig.Data.Pool
import Valaig.ForLean.Function

public section
namespace Valaig.Data

/--
  AbsMap is an abstraction of a mapping between keys and values (such as a hashmap or array).
  It is useful for proofs by allowing to abstract away from concrete details of a datastructure
  towards an idealised version.
-/
@[ext]
structure AbsMap (α : Type) (β : Type) [DecidableEq α] where
  raw ::
    valid : α -> Prop
    _decide : α -> Bool
    _decideLegal (key : α) : valid key ↔ _decide key = true
    map (key : α) (h : valid key) : β
    size : Nat

namespace AbsMap
variable {α : Type}

class AsNat (α : Type) where
  toNat : α -> Nat
  ofNat : Nat -> α
  ofNat_toNat : ∀ key, ofNat (toNat key) = key := by grind
  toNat_ofNat : ∀ n, toNat (ofNat n) = n := by grind

attribute [simp, grind =] AsNat.ofNat_toNat AsNat.toNat_ofNat
attribute [simp] AsNat.toNat AsNat.ofNat

variable [DecidableEq α] {β : Type} {map : AbsMap α β} {key : α} {value : β}

theorem ext' (a b : AbsMap α β)
    (valid : ∀ key, a.valid key = b.valid key)
    (map : ∀ key h, a.map key h = b.map key (by grind))
    (size : a.size = b.size) :
    a = b := by
  apply AbsMap.ext
  · grind
  · have := a._decideLegal
    have := b._decideLegal
    grind
  · apply hfunext
    · grind
    · intros
      apply hfunext
      · grind
      · grind
  · grind

@[always_inline]
instance : Membership α (AbsMap α β) where
  mem map key := map.valid key

@[always_inline]
instance : Decidable (map.valid key) :=
  have : map.valid key ↔ map._decide key := by simp [map._decideLegal]
  decidable_of_iff' _ this

@[always_inline]
instance : Decidable (key ∈ map) := by
  simp +instances only [instMembership]
  infer_instance

@[local grind =_]
theorem valid_iff :
    map.valid key ↔ key ∈ map := by
  rfl

@[always_inline]
instance : GetElem (AbsMap α β) α β (fun map key => key ∈ map) where
  getElem := AbsMap.map

@[local grind =_]
theorem map_eq (h : key ∈ map) :
    map.map key h = map[key]:= by
  rfl

structure Monotone (old new : AbsMap α β) : Prop where
  valid (key : α) : old.valid key → new.valid key
  map (key : α) (h : old.valid key) : old.map key h = new.map key (valid key h)
  sized : old.size ≤ new.size

@[always_inline]
instance : LE (AbsMap α β) where
  le := Monotone

@[simp, grind =]
theorem mono_iff {old new : AbsMap α β} :
    old.Monotone new ↔ old ≤ new := by
  rfl

instance : Std.IsPreorder (AbsMap α β) := by
  apply Std.IsPreorder.of_le
  <;> constructor
  · intros; constructor <;> simp
  · simp only [←mono_iff]; intros; constructor <;> grind only [Monotone]

section Monotone
variable {old new : AbsMap α β}

@[simp, grind .]
theorem mem_mono (mono : old ≤ new) (h : key ∈ old) :
    key ∈ new := by
  grind [mono.valid]

theorem getElem_mono (mono : old ≤ new) (h : key ∈ old) {h' : key ∈ new} :
    new[key]'h' = old[key] := by
  grind [mono.map]

grind_pattern getElem_mono => new[key], old ≤ new

@[simp, grind .]
theorem size_mono (mono : old ≤ new) :
    old.size ≤ new.size :=
  mono.sized

end Monotone

@[expose]
def mk (valid : α -> Prop) (map : (key : α) -> valid key -> β) (size : Nat) [DecidablePred valid] : AbsMap α β where
  valid := valid
  _decide key := Decidable.decide (valid key)
  _decideLegal := by grind
  map := map
  size := size

section mk
variable {valid : α -> Prop} {map : (key : α) -> valid key -> β} {size : Nat} [DecidablePred valid]

@[simp, grind =]
theorem valid_mk :
    (mk valid map size).valid = valid := by
  rfl

@[simp, grind =]
theorem map_mk :
    (mk valid map size).map = map := by
  rfl

@[simp, grind =]
theorem size_mk :
    (mk valid map size).size = size := by
  rfl

@[simp, grind =]
theorem mem_mk :
    key ∈ (mk valid map size) ↔ valid key := by
  rfl

@[simp, grind =]
theorem getElem_mk (mem : key ∈ mk valid map size) :
    (mk valid map size)[key]'mem = map key mem := by
  rfl

end mk

def empty : AbsMap α β :=
  .mk
    (valid := fun _ => False)
    (map := by grind)
    (size := 0)

section empty
attribute [local simp, local grind] empty

@[simp, grind =]
theorem size_empty :
    (empty : AbsMap α β).size = 0 := by
  grind

@[simp, grind .]
theorem mem_empty :
    key ∉ (empty : AbsMap α β) := by
  grind

@[simp, grind .]
theorem mono_empty (new : AbsMap α β) :
    empty ≤ new := by
  constructor <;> grind

end empty

set_option linter.unusedVariables false in
def push (map : AbsMap α β) (key : α) (value : β) (new : key ∉ map := by grind) : AbsMap α β :=
  .mk
    (valid := fun key' => key' ∈ map ∨ key = key')
    (map := fun key _ => if h : key ∈ map then map[key] else value)
    (size := map.size + 1)

section push
variable {key : α} {value : β} (new : key ∉ map)
attribute [local simp, local grind] push

@[simp, grind =]
theorem size_push :
    (map.push key value new).size = map.size + 1 := by
  grind

@[simp]
theorem mem_push_old {old : α} (h : old ∈ map) :
    old ∈ (map.push key value new) := by
  grind

@[simp]
theorem mem_push_self :
    key ∈ (map.push key value new) := by
  grind

@[simp, grind =]
theorem mem_push {key' : α} :
    key' ∈ (map.push key value new) ↔
    key' ∈ map ∨ key' = key := by
  grind

@[simp]
theorem getElem_push_old {old : α} (mem : old ∈ map) :
    (map.push key value new)[old] = map[old] := by
  grind

@[simp]
theorem getElem_push_self :
    (map.push key value new)[key] = value := by
  grind

@[simp, grind =]
theorem getElem_push {key' : α} (mem : key' ∈ map.push key value new) :
    (map.push key value new)[key'] =
    if _ : key' = key then value else map[key'] := by
  grind

@[simp, grind! .]
theorem mono_push :
    map ≤ map.push key value new := by
  constructor <;> grind [push]

end push

def insert (map : AbsMap α β) (key : α) (value : β) : AbsMap α β :=
  .mk
    (valid := fun key' => key' ∈ map ∨ key' = key)
    (map := fun key' _ => if _ : key' = key then value else map[key'])
    (size := if key ∈ map then map.size else map.size + 1)

section insert
variable {key : α} {value : β}
attribute [local simp, local grind] insert

@[simp]
theorem size_insert_mem (mem : key ∈ map) :
    (map.insert key value).size = map.size := by
  grind

@[simp]
theorem size_insert_not_mem (notmem : key ∉ map) :
    (map.insert key value).size = map.size + 1 := by
  grind

@[simp, grind =]
theorem size_insert :
    (map.insert key value).size = if key ∈ map then map.size else map.size + 1 := by
  grind

@[simp]
theorem mem_insert_old {old : α} (h : old ∈ map) :
    old ∈ (map.insert key value) := by
  grind

@[simp]
theorem mem_insert_self :
    key ∈ (map.insert key value) := by
  grind

@[simp, grind =]
theorem mem_insert {key' : α} :
    key' ∈ (map.insert key value) ↔
    key' ∈ map ∨ key' = key := by
  grind

@[simp]
theorem getElem_insert_old_not_mem {old : α} (mem : old ∈ map) (notmem : key ∉ map) :
    (map.insert key value)[old] = map[old] := by
  grind

@[simp]
theorem getElem_insert_self :
    (map.insert key value)[key] = value := by
  grind

@[simp, grind =]
theorem getElem_insert {key' : α} (mem : key' ∈ map.insert key value) :
    (map.insert key value)[key'] =
    if _ : key' = key then value else map[key'] := by
  grind

@[simp, grind! .]
theorem mono_insert (unused : key ∉ map) :
    map ≤ map.insert key value := by
  constructor <;> grind

@[simp, grind =]
theorem insert_eq_push  (new : key ∉ map) :
    map.insert key value = map.push key value := by
  unfold insert push
  apply ext' <;> grind

end insert

set_option linter.unusedVariables false in
def set (map : AbsMap α β) (key : α) (value : β) (mem : key ∈ map := by grind) : AbsMap α β :=
  { map with map key' _ := if key' = key then value else map[key'] }

section set
variable {key : α} {value : β} (mem : key ∈ map)
attribute [local simp, local grind] set

@[simp, grind =]
theorem size_set :
    (map.set key value mem).size = map.size := by
  grind

@[simp, grind =]
theorem mem_set {key' : α} :
    key' ∈ (map.set key value mem) ↔ key' ∈ map := by
  grind

@[simp]
theorem getElem_set_self :
    (map.set key value mem)[key] = value := by
  grind

@[simp, grind =]
theorem getElem_set {key' : α} (mem' : key' ∈ map.set key value mem) :
    (map.set key value mem)[key'] =
    have h : key' ∈ map := by grind
    if _ : key' = key then value else map[key']'h := by
  unfold set
  grind

end set

def modify (map : AbsMap α β) (key : α) (f : β -> β) : AbsMap α β :=
  { map with map key' _ := if key' = key then f map[key'] else map[key'] }

section modify
variable {key : α} (f : β -> β)
attribute [local simp, local grind] modify

@[simp, grind =]
theorem size_modify :
    (map.modify key f).size = map.size := by
  grind

@[simp, grind =]
theorem mem_modify {key' : α} :
    key' ∈ (map.modify key f) ↔ key' ∈ map := by
  grind

@[simp]
theorem getElem_modify_self (mem : key ∈ map) :
    (map.modify key f)[key] = f map[key] := by
  grind

@[simp, grind =]
theorem getElem_modify {key' : α} (mem' : key' ∈ map.modify key f) :
    (map.modify key f)[key'] =
    have h : key' ∈ map := by grind
    if _ : key' = key then f (map[key']'h) else (map[key']'h) := by
  unfold modify
  grind

end modify

def erase (map : AbsMap α β) (key : α) : AbsMap α β :=
  .mk
    (valid := fun key' => key ≠ key' ∧ map.valid key')
    (map := fun key' _ => map[key'])
    (size := if key ∈ map then map.size - 1 else map.size)

section erase
variable {key : α}
attribute [local simp, local grind] erase

@[simp, grind =]
theorem size_erase :
    (map.erase key).size = if key ∈ map then map.size - 1 else map.size := by
  grind

@[simp, grind =]
theorem mem_erase {key' : α} :
    key' ∈ map.erase key ↔ key' ≠ key ∧ key' ∈ map := by
  grind

@[simp, grind =]
theorem getElem_erase {key' : α} (mem' : key' ∈ map.erase key) :
    (map.erase key)[key'] =
    have h : key' ∈ map := by grind
    map[key']'h := by
  grind

end erase

set_option linter.unusedVariables false in
def move (map : AbsMap α β) (old new : α) (mem : old ∈ map := by grind) (notmem : new ∉ map ∨ new = old := by grind) : AbsMap α β :=
  .mk
    (valid := fun key => (map.valid key ∧ key ≠ old) ∨ key = new)
    (map := fun key valid => if _ : key = new then map[old] else map[key])
    (size := map.size)

section move
variable {old new : α} (mem : old ∈ map) (notmem : new ∉ map ∨ new = old)
attribute [local simp, local grind] move

@[simp, grind =]
theorem size_move :
    (map.move old new mem notmem).size = map.size := by
  grind

@[simp, grind =]
theorem mem_move {key : α} :
    key ∈ map.move old new mem notmem ↔
    (key ∈ map ∧ key ≠ old) ∨ key = new := by
  grind

@[simp, grind =]
theorem getElem_move {key : α} (mem' : key ∈ map.move old new mem notmem) :
    (map.move old new mem notmem)[key]'mem' =
    if _ : key = new then
      map[old]'mem
    else
      have h : key ∈ map := by grind
      map[key]'h := by
  grind

end move

def mapVal {γ : Type} (map : AbsMap α β) (f : β -> γ) : AbsMap α γ :=
  .mk
    (valid := map.valid)
    (map := fun key valid => f map[key])
    (size := map.size)

section mapVal
variable {γ : Type} {f : β -> γ} {key : α} {value : β}
attribute [local simp, local grind] mapVal

@[simp, grind =]
theorem size_mapVal :
    (map.mapVal f).size = map.size := by
  grind

@[simp, grind =]
theorem mem_mapVal :
    key ∈ (map.mapVal f) ↔ key ∈ map := by
  grind

@[simp, grind =]
theorem getElem_mapVal (mem : key ∈ map.mapVal f) :
    (map.mapVal f)[key] =
    have h : key ∈ map := by grind
    f map[key] := by
  grind

@[simp, grind =]
theorem mapVal_empty :
    (empty : AbsMap α β).mapVal f = (empty : AbsMap α γ) := by
  unfold mapVal empty
  apply ext' <;> grind

@[simp, grind =]
theorem mapVal_push (new : key ∉ map) :
    (map.push key value).mapVal f = (map.mapVal f).push key (f value) := by
  unfold mapVal push
  apply ext' <;> grind

@[simp, grind =]
theorem mapVal_insert :
    (map.insert key value).mapVal f = (map.mapVal f).insert key (f value) := by
  unfold mapVal insert
  apply ext' <;> grind

@[simp, grind =]
theorem mapVal_set (mem : key ∈ map) :
    (map.set key value).mapVal f = (map.mapVal f).set key (f value) := by
  unfold mapVal set
  apply ext' <;> grind

@[simp, grind =]
theorem mapVal_erase :
    (map.erase key).mapVal f = (map.mapVal f).erase key := by
  unfold mapVal erase
  apply ext' <;> grind

@[simp, grind =]
theorem mapVal_move {old new : α} mem notmem:
    (map.move old new mem notmem).mapVal f = (map.mapVal f).move old new := by
  unfold mapVal move
  apply ext' <;> grind

end mapVal

@[always_inline, expose]
def ofPool (pool : Pool β) (α : Type) [AsNat α] [DecidableEq α] : AbsMap α β :=
  .mk
    (valid := (AsNat.toNat · ∈ pool))
    (map := fun key valid => pool[AsNat.toNat key])
    (size := pool.size)

section ofPool
variable {pool : Pool β} [AsNat α]

@[simp, grind =]
theorem mem_ofPool :
    key ∈ ofPool pool α ↔ AsNat.toNat key ∈ pool := by
  rfl

@[simp, grind =]
theorem getElem_ofPool (mem : key ∈ ofPool pool α) :
    (ofPool pool α)[key]'mem = pool[AsNat.toNat key] := by
  rfl

@[simp, grind =]
theorem size_ofPool :
    (ofPool pool α).size = pool.size := by
  rfl

@[simp, grind =]
theorem ofPool_empty :
    ofPool (@Pool.empty β) α = .empty := by
  unfold ofPool empty
  apply ext' <;> grind

@[simp, grind =]
theorem ofPool_modify {idx : Nat} (f : β -> β) mem :
    ofPool (pool.modify idx f mem) α = (ofPool pool α).modify (AsNat.ofNat idx) f := by
  unfold ofPool modify
  apply ext' <;> grind

@[simp, grind =]
theorem ofPool_push {val : β} :
    ofPool (pool.push val) α = (ofPool pool α).push (AsNat.ofNat pool.nextIdx) val := by
  unfold ofPool push
  apply ext' <;> grind

@[simp, grind =]
theorem ofPool_erase [Inhabited β] {idx : Nat} mem :
    ofPool (pool.erase idx mem) α = (ofPool pool α).erase (AsNat.ofNat idx) := by
  unfold ofPool erase
  apply ext' <;> grind

@[simp, grind =]
theorem ofPool_move [Inhabited β] {old new : Nat} mem notmem :
    ofPool (pool.move old new mem notmem) α = (ofPool pool α).move (AsNat.ofNat old) (AsNat.ofNat new) := by
  unfold ofPool move
  apply ext' <;> grind

end ofPool

attribute [simp, grind =] valid_iff map_eq

end AbsMap
