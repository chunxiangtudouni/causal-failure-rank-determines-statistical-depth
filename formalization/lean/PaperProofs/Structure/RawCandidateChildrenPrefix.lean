module

public import PaperProofs.Structure.RawCandidateChildrenLayout

/-! Partial child scans and actual matched-write positions.  These facts
hold for arbitrary parent-word functions; the full-tree protocol is only
needed by the separate ChildrenLayout bridge. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateChildrenPrefix

open RawCandidateChildrenLayout

def childPrefix (_size : Nat) (words : Nat → Nat) (parent upto : Nat) : List Nat :=
  (List.range upto).filter (fun child => decide (words child = parent + 1))

def flatPrefix (size : Nat) (words : Nat → Nat) (upto : Nat) : List Nat :=
  (List.range upto).flatMap (childIDs size words)

theorem childPrefix_zero (size : Nat) (words : Nat → Nat) (parent : Nat) :
    childPrefix size words parent 0 = [] := rfl

theorem childPrefix_succ (size : Nat) (words : Nat → Nat) (parent upto : Nat) :
    childPrefix size words parent (upto + 1) =
      if words upto = parent + 1 then childPrefix size words parent upto ++ [upto]
      else childPrefix size words parent upto := by
  simp only [childPrefix, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil,
    decide_eq_true_eq]
  by_cases hmatch : words upto = parent + 1 <;> simp [hmatch]

theorem childPrefix_length_succ (size : Nat) (words : Nat → Nat) (parent upto : Nat) :
    (childPrefix size words parent (upto + 1)).length =
      (childPrefix size words parent upto).length + if words upto = parent + 1 then 1 else 0 := by
  rw [childPrefix_succ]
  by_cases hmatch : words upto = parent + 1 <;> simp [hmatch]

theorem childPrefix_full (size : Nat) (words : Nat → Nat) (parent : Nat) :
    childPrefix size words parent size = childIDs size words parent := rfl

theorem flatPrefix_zero (size : Nat) (words : Nat → Nat) : flatPrefix size words 0 = [] := rfl

theorem flatPrefix_succ (size : Nat) (words : Nat → Nat) (upto : Nat) :
    flatPrefix size words (upto + 1) = flatPrefix size words upto ++ childIDs size words upto := by
  simp only [flatPrefix, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem flatPrefix_full (size : Nat) (words : Nat → Nat) :
    flatPrefix size words size = flatChildren size words := rfl

theorem childPrefix_length_le_upto (size : Nat) (words : Nat → Nat) (parent upto : Nat) :
    (childPrefix size words parent upto).length ≤ upto := by
  simpa only [childPrefix, List.length_range] using
    List.length_filter_le (fun child => decide (words child = parent + 1)) (List.range upto)

theorem childPrefix_length_mono (size : Nat) (words : Nat → Nat) (parent before after : Nat)
    (hle : before ≤ after) :
    (childPrefix size words parent before).length ≤ (childPrefix size words parent after).length :=
  (List.Sublist.filter _ (List.range_sublist.mpr hle)).length_le

theorem flatPrefix_length_mono (size : Nat) (words : Nat → Nat) (before after : Nat) (hle : before ≤ after) :
    (flatPrefix size words before).length ≤ (flatPrefix size words after).length :=
  (List.Sublist.flatMap (List.range_sublist.mpr hle) (childIDs size words)).length_le

theorem partial_span_le_total (size : Nat) (words : Nat → Nat) (parent upto : Nat)
    (hparent : parent < size) (hupto : upto ≤ size) :
    (flatPrefix size words parent).length + (childPrefix size words parent upto).length ≤
      (flatChildren size words).length := by
  have hchildren := childPrefix_length_mono size words parent upto size hupto
  rw [childPrefix_full] at hchildren
  have hflat := flatPrefix_length_mono size words (parent + 1) size (by omega)
  rw [flatPrefix_succ, List.length_append, flatPrefix_full] at hflat
  omega

/-- Only a true match writes a new child word.  At that point the current
flat output position is strictly inside the final flat list, even for an
arbitrary parent-word function. -/
theorem matched_write_lt_total (size : Nat) (words : Nat → Nat) (parent child : Nat)
    (hparent : parent < size) (hchild : child < size) (hmatch : words child = parent + 1) :
    (flatPrefix size words parent).length + (childPrefix size words parent child).length <
      (flatChildren size words).length := by
  have hspan := partial_span_le_total size words parent (child + 1) hparent (by omega)
  simp only [childPrefix_length_succ, hmatch, ite_true] at hspan
  omega

theorem childPrefix_getD_succ_old (size : Nat) (words : Nat → Nat) (parent upto position : Nat)
    (hposition : position < (childPrefix size words parent upto).length) :
    (childPrefix size words parent (upto + 1)).getD position 0 =
      (childPrefix size words parent upto).getD position 0 := by
  rw [childPrefix_succ]
  by_cases hmatch : words upto = parent + 1
  · simp only [hmatch, ite_true]
    exact List.getD_append _ _ _ _ hposition
  · simp only [hmatch, ite_false]

theorem childPrefix_getD_succ_new (size : Nat) (words : Nat → Nat) (parent upto : Nat)
    (hmatch : words upto = parent + 1) :
    (childPrefix size words parent (upto + 1)).getD (childPrefix size words parent upto).length 0 = upto := by
  rw [childPrefix_succ]
  simp only [hmatch, ite_true]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  rfl

theorem flatPrefix_getD_succ_old (size : Nat) (words : Nat → Nat) (parent position : Nat)
    (hposition : position < (flatPrefix size words parent).length) :
    (flatPrefix size words (parent + 1)).getD position 0 = (flatPrefix size words parent).getD position 0 := by
  rw [flatPrefix_succ]
  exact List.getD_append _ _ _ _ hposition

theorem flatPrefix_getD_succ_new (size : Nat) (words : Nat → Nat) (parent position : Nat) :
    (flatPrefix size words (parent + 1)).getD ((flatPrefix size words parent).length + position) 0 =
      (childIDs size words parent).getD position 0 := by
  rw [flatPrefix_succ, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

end PaperProofs.Structure.LaminarTree.RawCandidateChildrenPrefix
