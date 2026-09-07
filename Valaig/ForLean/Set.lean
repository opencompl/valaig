module

@[expose] public section
namespace Valaig
variable {α : Type u}

/--
  Basic set definition as a predicate on a type.
-/
def Set (α : Type u) :=
  α -> Prop

namespace Set
variable {s : Set α} {a : α}

def ofFn (f : α -> Prop) : Set α :=
  f

instance : Membership α (Set α) where
  mem s a := s a

@[local grind =]
theorem mem_iff :
    a ∈ s ↔ s a := by
  rfl

@[simp, grind =]
theorem mem_ofFn {f : α -> Prop} :
    a ∈ ofFn f ↔ f a := by
  rfl

@[ext, grind ext]
theorem ext_mem {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) :
    a = b := by
  funext x
  simp [←mem_iff, h]

def compl (set : Set α) : Set α :=
  (· ∉ set)

@[simp, grind =]
theorem mem_compl :
    a ∈ s.compl ↔ a ∉ s := by
  grind [compl]

def filter (set : Set α) (p : α -> Prop) : Set α :=
  fun x => x ∈ set ∧ p x

@[simp, grind =]
theorem mem_filter {p : α -> Prop} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a := by
  grind [filter]

def empty : Set α :=
  fun _ => False

@[simp, grind .]
theorem mem_empty :
    a ∉ empty := by
  grind [empty]

instance : Inhabited (Set α) where
  default := empty

def bottom : Set α :=
  empty

@[simp, grind =]
theorem bottom_eq :
    (bottom : Set α) = empty := by
  rfl

def top : Set α :=
  bottom.compl

@[simp, grind .]
theorem mem_top :
    a ∈ top := by
  simp [top]

instance : EmptyCollection (Set α) where
  emptyCollection := bottom

@[simp]
theorem emptyCollection_eq :
    (EmptyCollection.emptyCollection : Set α) = bottom := by
  rfl

instance : Insert α (Set α) where
  insert a s := fun x => x ∈ s ∨ x = a

@[simp, grind =]
theorem mem_insert {x : α} :
    a ∈ insert x s ↔ a ∈ s ∨ a = x := by
  rfl

instance : Singleton α (Set α) where
  singleton a := (· = a)

@[simp, grind =]
theorem mem_singleton {x : α} :
    a ∈ (singleton x : Set α) ↔ a = x := by
  rfl

instance : LawfulSingleton α (Set α) where
  insert_empty_eq := by simp; grind

instance : HasSubset (Set α) where
  Subset a b := ∀ x ∈ a, x ∈ b

instance : HasSSubset (Set α) where
  SSubset a b := a ⊆ b ∧ ∃ x ∈ b, x ∉ a

instance : Union (Set α) where
  union a b := fun x => x ∈ a ∨ x ∈ b

@[simp, grind =]
theorem mem_union {a b : Set α} {x : α} :
    x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := by
  rfl

instance : Inter (Set α) where
  inter a b := fun x => x ∈ a ∧ x ∈ b

@[simp, grind =]
theorem mem_inter {a b : Set α} {x : α} :
    x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := by
  rfl

instance : SDiff (Set α) where
  sdiff a b := fun x => x ∈ a ∧ x ∉ b

@[simp, grind =]
theorem mem_sdiff {a b : Set α} {x : α} :
    x ∈ a \ b ↔ x ∈ a ∧ x ∉ b := by
  rfl

instance : Pure Set where
  pure a := singleton a

@[simp, grind =]
theorem mem_pure {x : α} :
    (pure x : Set α) = singleton x := by
  rfl

instance : Bind Set where
  bind s f := fun b => ∃ a ∈ s, b ∈ f a

@[simp, grind =]
theorem mem_bind {β : Type u} {x : β} {f : α -> Set β} :
    x ∈ (s >>= f) ↔ ∃ a ∈ s, x ∈ f a := by
  rfl

def map {β : Type v} (s : Set α) (f : α -> β) : Set β :=
  fun b => ∃ a ∈ s, b = f a

@[simp, grind =]
theorem mem_map {β : Type v} {x : β} {f : α -> β} :
    x ∈ s.map f ↔ ∃ a ∈ s, x = f a := by
  rfl

instance : Functor Set where
  map f s := s.map f

@[simp, grind =]
theorem functor_map_eq {β : Type u} {f : α -> β} :
    map s f = s.map f := by
  rfl

instance : LawfulFunctor Set where
  map_const := by simp +instances [instFunctor]
  id_map := by simp +instances only [instFunctor]; grind
  comp_map := by simp +instances only [instFunctor]; grind

end Valaig.Set
