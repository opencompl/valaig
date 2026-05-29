module

public section
namespace Array

variable {α : Type}

/-
`Array.modify` doesn't provide a proof that the element being modified corresponds to the index,
but this is often useful so we provide our own implementation, and the unsafe implementation for
performance
-/

@[inline]
private unsafe def modifyMemUnsafe (xs : Array α) (i : Nat) (h : i < xs.size)
    (f : { a : α // xs[i] = a } → α) : Array α :=
  let v := xs[i]
  -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
  -- Note: we assume that arrays have a uniform representation irrespective
  -- of the element type, and that it is valid to store `box(0)` in any array.
  let xs' := xs.set i (unsafeCast ())
  let v := f ⟨v, by trivial⟩
  xs'.set i v (by rwa [size_set h])

@[implemented_by modifyMemUnsafe]
def modifyMem (xs : Array α) (i : Nat) (h : i < xs.size) (f : { a : α // xs[i] = a } → α) : Array α :=
  xs.set i (f ⟨xs[i], by trivial⟩) h

@[simp, grind =]
theorem modifyMem_def {xs : Array α} {i : Nat} (h : i < xs.size) (f : { a : α // xs[i] = a } → α) :
    xs.modifyMem i h f = xs.set i (f ⟨xs[i], by trivial⟩) h := by
  rw [modifyMem]

@[simp, grind =]
theorem size_modifyMem {xs : Array α} {i : Nat} (h : i < xs.size) (f : { a : α // xs[i] = a } → α) :
    (xs.modifyMem i h f).size = xs.size := by
  rw [modifyMem_def, size_set]

section
variable {xs xs' : Array α} {i : Nat} {f : (i : Nat) → (h : i < xs.size) → (a : α) → xs[i] = a → α}
variable {hstep : ∃ h1 h2, xs'[i]'h1 = xs[i]'h2}

@[always_inline]
private def mapMem.step {xs : Array α} (xs' : Array α) (i : Nat)
      (f : (i : Nat) → (h : i < xs.size) → (a : α) → xs[i] = a → α)
      (h : ∃ h1 h2, xs'[i]'h1 = xs[i]'h2) : Array α :=
    have hxs : i < xs.size := by lia
    have hxs' : i < xs'.size := by lia
    xs'.modifyMem i hxs' fun ⟨x, p⟩ =>
      f i hxs x (by simp_all)

private theorem mapMem.step.size_eq : (step xs' i f hstep).size = xs'.size := by
  grind only [step, size_modifyMem]

private theorem mapMem.step.eq_above {j : Nat} (h1 : j > i) (h2 : j < xs'.size) :
    have h := by grind only [size_eq]
    (step xs' i f hstep)[j]'h = xs'[j] := by
  grind only [getElem_set, step, modifyMem_def]

private theorem mapMem.step.eq_above' {j : Nat} (h1 : j > i) (h2 : j < xs'.size)
    (h3 : xs.size = xs'.size) (_ : xs[j] = xs'[j]) :
    have h := by grind only [size_eq]
    have h' := by grind only [size_eq]
    (step xs' i f hstep)[j]'h = xs[j]'h' := by
  grind only [eq_above]

-- TODO: This can be specialized to use usize for the iterator and also made possible to return
-- different type
@[inline]
def mapMem (xs : Array α) (f : (i : Nat) → (h : i < xs.size) → (a : α) → xs[i] = a → α) : Array α :=
  @go xs 0 (by omega) (by simp)
where
  go (xs' : Array α) (i : Nat) (hsize : xs'.size = xs.size)
      (heq : ∀ {j} (_ : j ≥ i) (_ : j < xs.size), xs'[j] = xs[j]) :
      Array α :=
    if h : i ≥ xs'.size then
      xs'
    else
      let xs' := mapMem.step xs' i f (by grind only)

      have hsize := by rwa [mapMem.step.size_eq]
      have heq : ∀ {j} (_ : j ≥ i + 1), _ := by grind only [mapMem.step.eq_above]
      @go xs' (i + 1) hsize heq
  termination_by xs.size - i

variable {hsize : xs'.size = xs.size}
variable {hgo : ∀ {j} (_ : j ≥ i) (_ : j < xs.size), xs'[j] = xs[j]}

private theorem mapMem.go.size_eq : (go xs f xs' i hsize hgo).size = xs'.size := by
  unfold go
  induction h : (xs.size - i) generalizing xs' i with
  | zero => lia
  | succ fuel motive =>
    split
    · lia
    · rw [go, @motive (xs' := step xs' i f (by grind))]
      · exact step.size_eq
      · rwa [step.size_eq]
      · grind only [mapMem.step.eq_above]
      · omega

private theorem mapMem.go.getElem {j : Nat} (h : j < xs'.size) :
    (go xs f xs' i hsize hgo)[j]'(by grind only [go.size_eq]) =
      if _ : j ≥ i then
        f j (by omega) (xs[j]'(by omega)) rfl
      else
        xs'[j] := by
  unfold go
  induction h : (xs.size - i) generalizing xs' i with
  | zero => lia
  | succ fuel motive =>
    split
    · omega
    · simp only
      unfold go
      rw [@motive (xs' := step xs' i f (by grind only))]
      · grind [step]
      · grind [step.size_eq]
      · grind [mapMem.step.eq_above]
      · grind [step.size_eq]
      · grind

@[simp, grind =]
theorem size_mapMem : (xs.mapMem f).size = xs.size := by
  apply mapMem.go.size_eq
  lia

@[simp, grind →]
theorem getElem_mapMem {i : Nat} (f : (i : Nat) → (h : i < xs.size) → (a : α) → xs[i] = a → α) (hi : i < (xs.mapMem f).size) :
    have h : i < xs.size := by simp_all
    (xs.mapMem f)[i] = f i h xs[i] rfl := by
  unfold mapMem
  apply mapMem.go.getElem
  · intros; rfl
  · rwa [size_mapMem] at hi

end

@[inline]
def resize (xs : Array α) (size : Nat) (elem : α) : Array α :=
  if _ : xs.size = size then
    xs
  else if _ : xs.size < size then
    extend xs
  else
    reduce xs
where
  extend (xs : Array α) (le : xs.size ≤ size := by grind) : Array α :=
    if _ : xs.size = size then
      xs
    else
      extend (xs.push elem)

  reduce (xs : Array α) (le : size ≤ xs.size := by grind) : Array α :=
    if _ : xs.size = size then
      xs
    else
      reduce xs.pop

section resize
variable {size : Nat} {elem : α} {xs : Array α}

@[simp, grind =]
private theorem resize.size_extend le :
    (resize.extend size elem xs le).size = size := by
  fun_induction resize.extend <;> grind

@[simp, grind =]
private theorem resize.getElem_extend le {idx : Nat} (mem : idx < (resize.extend size elem xs le).size) :
    (resize.extend size elem xs le)[idx]'mem =
    if _ : idx < xs.size then
      xs[idx]
    else
      elem := by
  fun_induction resize.extend <;> grind

@[simp, grind =]
private theorem resize.size_reduce le :
    (resize.reduce size xs le).size = size := by
  fun_induction resize.reduce <;> grind

@[simp, grind =]
private theorem resize.getElem_reduce le {idx : Nat} (mem : idx < (resize.reduce size xs le).size) :
    (resize.reduce size xs le)[idx]'mem = xs[idx]'(by grind) := by
  fun_induction resize.reduce <;> (unfold reduce; grind)

@[simp, grind =]
theorem size_resize :
    (xs.resize size elem).size = size := by
  grind [resize]

@[simp, grind =]
private theorem getElem_resize {idx : Nat} (mem : idx < (xs.resize size elem).size) :
    (xs.resize size elem)[idx]'mem =
    if _ : idx < xs.size then
      xs[idx]
    else
      elem := by
  grind [resize]

end resize

end Array
