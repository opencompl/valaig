module

public import Std.Data.Iterators.Lemmas

public section

/-
This module just marks some useful iterator based simp lemmas as grind, making them more useful.
-/

-- Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
attribute [simp, grind =]
  Std.IterM.toList_filterMap
  Std.IterM.toList_mapM
  Std.IterM.toList_map
  Std.IterM.toList_filter
  Std.IterM.toListRev_filterMap
  Std.IterM.toListRev_map
  Std.IterM.toListRev_filter
  Std.IterM.toArray_filterMap
  Std.IterM.toArray_mapM
  Std.IterM.toArray_map
  Std.IterM.toArray_filter
  Std.IterM.forIn_filterMapM
  Std.IterM.forIn_filterMap
  Std.IterM.forIn_mapM
  Std.IterM.forIn_map
  Std.IterM.forIn_filterM
  Std.IterM.forIn_filter
  Std.IterM.foldM_filterMapM
  Std.IterM.foldM_mapM
  Std.IterM.foldM_filterM
  Std.IterM.foldM_filterMap
  Std.IterM.foldM_map
  Std.IterM.foldM_filter
  Std.IterM.fold_filterMapM
  Std.IterM.fold_mapM
  Std.IterM.fold_filterM
  Std.IterM.fold_filterMap
  Std.IterM.fold_map
  Std.IterM.fold_filter
  Std.IterM.length_map
  Std.IterM.anyM_filterMap
  Std.IterM.anyM_map
  Std.IterM.anyM_filter
  Std.IterM.any_filterMap
  Std.IterM.any_map
  Std.IterM.allM_filterMap
  Std.IterM.allM_map
  Std.IterM.allM_filter
  Std.IterM.all_filterMap
  Std.IterM.all_map

-- Init.Data.Iterators.Lemmas.Combinators.Monadic.FlatMap
attribute [simp, grind =]
  Std.IterM.toList_flatMapAfterM
  Std.IterM.toArray_flatMapAfterM
  Std.IterM.toList_flatMapM
  Std.IterM.toArray_flatMapM
  Std.IterM.toList_flatMapAfter
  Std.IterM.toArray_flatMapAfter
  Std.IterM.toList_flatMap
  Std.IterM.toArray_flatMap

-- Init.Data.Iterators.Lemmas.Combinators.Monadic.Take
attribute [simp, grind =]
  Std.IterM.toList_take_zero
  Std.IterM.toList_toTake

-- Init.Data.Iterators.Lemmas.Combinators.FilterMap
attribute [simp, grind =]
  Std.Iter.toList_filterMap
  Std.Iter.toList_mapM
  Std.Iter.toList_map
  Std.Iter.toList_filter
  Std.Iter.toListRev_filterMap
  Std.Iter.toListRev_map
  Std.Iter.toListRev_filter
  Std.Iter.toArray_filterMap
  Std.Iter.toArray_mapM
  Std.Iter.toArray_map
  Std.Iter.toArray_filter
  Std.Iter.forIn_filterMapM
  Std.Iter.forIn_filterMap
  Std.Iter.forIn_mapM
  Std.Iter.forIn_map
  Std.Iter.forIn_filterM
  Std.Iter.forIn_filter
  Std.Iter.foldM_filterMapM
  Std.Iter.foldM_mapM
  Std.Iter.foldM_filterM
  Std.Iter.foldM_filterMap
  Std.Iter.foldM_map
  Std.Iter.foldM_filter
  Std.Iter.fold_filterMapM
  Std.Iter.fold_mapM
  Std.Iter.fold_filterM
  Std.Iter.fold_filterMap
  Std.Iter.fold_map
  Std.Iter.fold_filter
  Std.Iter.length_map
  Std.Iter.anyM_filterMap
  Std.Iter.anyM_map
  Std.Iter.anyM_filter
  Std.Iter.any_filterMap
  Std.Iter.any_map
  Std.Iter.allM_filterMap
  Std.Iter.allM_map
  Std.Iter.allM_filter
  Std.Iter.all_mapM
  Std.Iter.all_filterMap
  Std.Iter.all_map

-- Init.Data.Iterators.Lemmas.Combinators.FlatMap
attribute [simp, grind =]
  Std.Iter.toList_flatMapAfterM
  Std.Iter.toArray_flatMapAfterM
  Std.Iter.toList_flatMapM
  Std.Iter.toArray_flatMapM
  Std.Iter.toList_flatMapAfter
  Std.Iter.toArray_flatMapAfter
  Std.Iter.toList_flatMap
  Std.Iter.toArray_flatMap

-- Init.Data.Iterators.Lemmas.Combinators.Take
attribute [simp, grind =]
  Std.Iter.toList_take_of_finite
  Std.Iter.toListRev_take_of_finite
  Std.Iter.toArray_take_of_finite
  Std.Iter.toList_take_zero
  Std.Iter.toList_toTake

-- Init.Data.Iterators.Lemmas.Consumers.Combinators.Collect
attribute [simp, grind =]
  Std.IterM.toArray_ensureTermination
  Std.IterM.toList_ensureTermination
  Std.IterM.toListRev_ensureTermination_eq_toListRev
  Std.IterM.toList_toArray
  Std.IterM.toList_toArray_ensureTermination
  Std.IterM.toArray_toList
  Std.IterM.toArray_toList_ensureTermination
  Std.IterM.reverse_toListRev
  Std.IterM.reverse_toListRev_ensureTermination
  Std.IterM.toListRev_eq
  Std.IterM.toListRev_ensureTermination

-- Init.Data.Iterators.Lemmas.Consumers.Collect
attribute [simp, grind =]
  Std.Iter.toArray_ensureTermination
  Std.Iter.toList_ensureTermination
  Std.Iter.toListRev_ensureTermination_eq_toListRev
  Std.Iter.toList_toArray
  Std.Iter.toList_toArray_ensureTermination
  Std.Iter.toArray_toList
  Std.Iter.toArray_toList_ensureTermination
  Std.Iter.reverse_toListRev
  Std.Iter.reverse_toListRev_ensureTermination
  Std.Iter.toListRev_eq
  Std.Iter.toListRev_ensureTermination

-- Init.Data.Iterators.Lemmas.Consumers.Loop
attribute [simp, grind =]
  Std.Iter.size_toArray_eq_length
  Std.Iter.length_toList_eq_length
  Std.Iter.length_toListRev_eq_length

-- Init.Data.Iterators.Lemmas.Producers.Monadic.List
attribute [simp, grind =]
  List.step_iterM_nil
  List.step_iterM_cons
  List.step_iterM
  List.toArray_iterM
  List.toList_iterM
  List.toListRev_iterM

-- Init.Data.Iterators.Lemmas.Producers.List
attribute [simp, grind =]
  List.step_iter_nil
  List.step_iter_cons
  List.toArray_iter
  List.toList_iter
  List.toListRev_iter

-- Std.Data.Iterators.Lemmas.Combinators.Drop
attribute [simp, grind =]
  Std.Iter.toList_drop
  Std.Iter.toListRev_drop
  Std.Iter.toArray_drop

-- Std.Data.Iterators.Lemmas.Combinators.DropWhile
attribute [simp, grind =]
  Std.Iter.toList_dropWhile_of_finite
  Std.Iter.toArray_dropWhile_of_finite
  Std.Iter.toListRev_dropWhile_of_finite

-- Std.Data.Iterators.Lemmas.Combinators.TakeWhile
attribute [simp, grind =]
  Std.Iter.toList_takeWhile_of_finite
  Std.Iter.toListRev_takeWhile_of_finite
  Std.Iter.toArray_takeWhile_of_finite

-- Std.Data.Iterators.Lemmas.Combinators.Zip
attribute [simp, grind =]
  Std.Iter.toList_zip_of_finite
  Std.Iter.toListRev_zip_of_finite
  Std.Iter.toArray_zip_of_finite
  Std.Iter.toList_take_zip
  Std.Iter.toListRev_take_zip
  Std.Iter.toArray_take_zip

-- Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect
attribute [simp, grind =>]
  Std.IterM.Equiv.toListRev_eq
  Std.IterM.Equiv.toList_eq
  Std.IterM.Equiv.toArray_eq

-- Std.Data.Iterators.Lemmas.Consumers.Monadic.Loop
attribute [simp, grind =>]
  Std.IterM.Equiv.forIn_eq
  Std.IterM.Equiv.foldM_eq
  Std.IterM.Equiv.fold_eq
  Std.IterM.Equiv.drain_eq

-- Std.Data.Iterators.Lemmas.Consumers.Monadic.Loop
attribute [simp, grind =]
  Std.IterM.toHashSet_eq_fold
  Std.IterM.toExtHashSet_eq_ofList
  Std.IterM.toTreeSet_eq_fold
  Std.IterM.toExtTreeSet_eq_ofList

-- Std.Data.Iterators.Lemmas.Consumers.Collect
attribute [simp, grind =>]
  Std.Iter.Equiv.toListRev_eq
  Std.Iter.Equiv.toList_eq
  Std.Iter.Equiv.toArray_eq

-- Std.Data.Iterators.Lemmas.Consumers.Loop
attribute [simp, grind =>]
  Std.Iter.Equiv.forIn_eq
  Std.Iter.Equiv.foldM_eq
  Std.Iter.Equiv.fold_eq

-- Std.Data.Iterators.Lemmas.Consumers.Set
attribute [simp, grind =]
  Std.Iter.toExtHashSet_eq_ofList
  Std.Iter.toExtTreeSet_eq_ofList
attribute [grind! .]
  Std.Iter.toHashSet_equiv_ofList
  Std.Iter.toTreeSet_equiv_ofList

-- Std.Data.Iterators.Lemmas.Producers.Monadic.Array
attribute [simp, grind =]
  Array.toList_iterFromIdxM
  Array.toList_iterM
  Array.toArray_iterFromIdxM
  Array.toArray_iterM
  Array.toListRev_iterFromIdxM
  Array.toListRev_iterM
  Array.length_iterFromIdxM
  Array.length_iterM

-- Std.Data.Iterators.Lemmas.Producers.Monadic.Empty
attribute [simp, grind =]
  Std.IterM.step_empty
  Std.IterM.toList_empty
  Std.IterM.toListRev_empty
  Std.IterM.toArray_empty
  Std.IterM.forIn_empty
  Std.IterM.foldM_empty
  Std.IterM.fold_empty
  Std.IterM.drain_empty

-- Std.Data.Iterators.Lemmas.Producers.Monadic.Vector
attribute [simp, grind =]
  Vector.iterFromIdxM_toArray
  Vector.iterM_toArray
  Vector.toList_iterFromIdxM
  Vector.toList_iterM
  Vector.toArray_iterFromIdxM
  Vector.toArray_iterM
  Vector.toListRev_iterFromIdxM
  Vector.toListRev_iterM
  Vector.length_iterFromIdxM
  Vector.length_iterM

-- Std.Data.Iterators.Lemmas.Producers.Array
attribute [simp, grind =]
  Array.toList_iterFromIdx
  Array.toList_iter
  Array.toArray_iterFromIdx
  Array.toArray_iter
  Array.toListRev_iterFromIdx
  Array.toListRev_iter
  Array.length_iterFromIdx
  Array.length_iter

-- Std.Data.Iterators.Lemmas.Producers.Empty
attribute [simp, grind =]
  Std.Iter.toIterM_empty
  Std.Iter.step_empty
  Std.Iter.toList_empty
  Std.Iter.toListRev_empty
  Std.Iter.toArray_empty
  Std.Iter.forIn_empty
  Std.Iter.foldM_empty
  Std.Iter.fold_empty

-- Std.Data.Iterators.Lemmas.Producers.Range
attribute [simp, grind =]
  Std.Rcc.toList_iter
  Std.Rcc.toArray_iter
  Std.Rcc.length_iter
  Std.Rco.toList_iter
  Std.Rco.toArray_iter
  Std.Rco.length_iter
  Std.Rci.toList_iter
  Std.Rci.toArray_iter
  Std.Rci.length_iter
  Std.Roc.toList_iter
  Std.Roc.toArray_iter
  Std.Roc.length_iter
  Std.Roo.toList_iter
  Std.Roo.toArray_iter
  Std.Roo.length_iter
  Std.Roi.toList_iter
  Std.Roi.toArray_iter
  Std.Roi.length_iter
  Std.Ric.toList_iter
  Std.Ric.toArray_iter
  Std.Ric.length_iter
  Std.Rio.toList_iter
  Std.Rio.toArray_iter
  Std.Rio.length_iter
  Std.Rii.toList_iter
  Std.Rii.toArray_iter
  Std.Rii.length_iter

-- Std.Data.Iterators.Lemmas.Producers.Repeat
attribute [simp, grind =]
  Std.Iter.atIdxSlow?_repeat
  Std.Iter.toList_take_repeat_succ

-- Std.Data.Iterators.Lemmas.Producers.Slice
attribute [simp, grind =]
  Std.Slice.forIn_iter
  Std.Slice.foldlM_iter
  Std.Slice.foldl_iter
  Std.Slice.length_iter_eq_size
  Std.Slice.toArray_iter
  Std.Slice.toList_iter
  Std.Slice.toListRev_iter
  Std.Slice.fold_iter
  Std.Slice.foldM_iter

-- Std.Data.Iterators.Lemmas.Producers.Vector
attribute [simp, grind =]
  Vector.iterFromIdx_toArray
  Vector.iter_toArray
  Vector.toList_iterFromIdx
  Vector.toList_iter
  Vector.toArray_iterFromIdx
  Vector.toArray_iter
  Vector.toListRev_iterFromIdx
  Vector.toListRev_toIter
  Vector.length_iterFromIdx
  Vector.length_iter
