module

public section
namespace List

variable {α : Type u} {l : List α}

@[simp, grind .]
theorem nodup_attachWith (p : α -> Prop) h (nodup : l.Nodup) :
    (l.attachWith p h).Nodup := by
  grind [pairwise_iff_getElem]

@[simp, grind .]
theorem nodup_filter (p : α -> Bool) (nodup : l.Nodup) :
    (l.filter p).Nodup := by
  grind [pairwise_iff_getElem]

end List
