module

public import PaperProofs.Structure.RawCandidateStableOrder
public import PaperProofs.Structure.IndexedNodeCache

/-! Exact count-based positions for the original retained raw candidates.
The count only compares candidate cardinalities and original IDs.  The
proof identifies these positions with the already verified stable order;
it does not implement or assume a machine sorting routine. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateRankPositions

open RawCandidateOrder RawCandidateStableOrder

def Precedes (q : Nat) (full : List (Finset (Fin q))) (left right : Nat) : Prop :=
  candidateCard q full left < candidateCard q full right ∨
    candidateCard q full left = candidateCard q full right ∧ left < right

instance (q : Nat) (full : List (Finset (Fin q))) (left right : Nat) :
    Decidable (Precedes q full left right) := by
  unfold Precedes
  infer_instance

def lessCount (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) : Nat :=
  ((retainedCandidateIndices q full).filter (fun other => decide (Precedes q full other candidate))).length

private theorem filter_precedes_length_eq_idxOf (q : Nat) (full : List (Finset (Fin q)))
    (ids : List Nat)
    (hordered : ids.Pairwise (fun left right =>
      candidateCard q full left < candidateCard q full right ∨
        candidateCard q full left = candidateCard q full right ∧ left ≤ right))
    (candidate : Nat) (hmem : candidate ∈ ids) :
    (ids.filter (fun other => decide (Precedes q full other candidate))).length = ids.idxOf candidate := by
  induction ids with
  | nil => cases hmem
  | cons first tail ih =>
    obtain ⟨hfirst, htail⟩ := List.pairwise_cons.mp hordered
    by_cases heq : candidate = first
    · subst candidate
      have hself : ¬ Precedes q full first first := by simp only [Precedes]; omega
      have hfiltered : tail.filter (fun other => decide (Precedes q full other first)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other hother
        have horder := hfirst other hother
        have hnot : ¬ Precedes q full other first := by unfold Precedes; omega
        simpa only [decide_eq_true_eq] using hnot
      simp only [List.filter_cons, decide_eq_true_eq, hself, ite_false, hfiltered,
        List.length_nil, List.idxOf_cons_self]
    · have htailmem : candidate ∈ tail := (List.mem_cons.mp hmem).resolve_left heq
      have horder := hfirst candidate htailmem
      have hbefore : Precedes q full first candidate := by unfold Precedes; omega
      simp only [List.filter_cons, decide_eq_true_eq, hbefore, ite_true, List.length_cons]
      rw [List.idxOf_cons_ne tail (Ne.symm heq), ih htail htailmem]

theorem lessCount_eq_idxOf (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat)
    (hmem : candidate ∈ retainedCandidateIndices q full) :
    lessCount q full candidate = (sortedCandidateIndices q full).idxOf candidate := by
  have hperm := sortedCandidateIndices_perm q full
  have hlength := (hperm.filter (fun other => decide (Precedes q full other candidate))).length_eq
  have hsortedmem : candidate ∈ sortedCandidateIndices q full := hperm.mem_iff.mpr hmem
  exact hlength.symm.trans (filter_precedes_length_eq_idxOf q full _
    (sortedCandidateIndices_pairwise q full) candidate hsortedmem)

theorem sortedCandidateIndices_nodup (q : Nat) (full : List (Finset (Fin q))) :
    (sortedCandidateIndices q full).Nodup := by
  have hretained : (retainedCandidateIndices q full).Nodup := List.nodup_range.filter _
  exact hretained.perm (sortedCandidateIndices_perm q full).symm

theorem sortedCandidateIndices_length (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (sortedCandidateIndices q full).length = (prepareNormalization q full).indexed.nodes.size := by
  change (sortedCandidateIndices q full).length = (prepareNormalization q full).order.toArray.size
  rw [List.size_toArray]
  simpa only [List.length_map] using congrArg List.length (sortedCandidateSupports_eq_preparedOrder q full hq)

theorem lessCount_injective (q : Nat) (full : List (Finset (Fin q))) (left right : Nat)
    (hleft : left ∈ retainedCandidateIndices q full) (hright : right ∈ retainedCandidateIndices q full)
    (heq : lessCount q full left = lessCount q full right) : left = right := by
  apply (List.idxOf_inj ((sortedCandidateIndices_perm q full).mem_iff.mpr hleft)).mp
  rw [← lessCount_eq_idxOf q full left hleft, ← lessCount_eq_idxOf q full right hright]
  exact heq

theorem lessCount_ne_of_ne (q : Nat) (full : List (Finset (Fin q))) (left right : Nat)
    (hleft : left ∈ retainedCandidateIndices q full) (hright : right ∈ retainedCandidateIndices q full)
    (hne : left ≠ right) : lessCount q full left ≠ lessCount q full right :=
  fun heq => hne (lessCount_injective q full left right hleft hright heq)

theorem lessCount_lt_size (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (candidate : Nat) (hmem : candidate ∈ retainedCandidateIndices q full) :
    lessCount q full candidate < (prepareNormalization q full).indexed.nodes.size := by
  rw [lessCount_eq_idxOf q full candidate hmem, ← sortedCandidateIndices_length q full hq]
  exact List.idxOf_lt_length_of_mem ((sortedCandidateIndices_perm q full).mem_iff.mpr hmem)

theorem existsUnique_candidate_at_position (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (position : Nat) (hposition : position < (prepareNormalization q full).indexed.nodes.size) :
    ∃! candidate, candidate ∈ retainedCandidateIndices q full ∧ lessCount q full candidate = position := by
  have hp : position < (sortedCandidateIndices q full).length := by
    rw [sortedCandidateIndices_length q full hq]
    exact hposition
  let candidate := (sortedCandidateIndices q full)[position]
  have hsortedmem : candidate ∈ sortedCandidateIndices q full := List.getElem_mem hp
  have hmem : candidate ∈ retainedCandidateIndices q full :=
    (sortedCandidateIndices_perm q full).mem_iff.mp hsortedmem
  have hcount : lessCount q full candidate = position := by
    rw [lessCount_eq_idxOf q full candidate hmem]
    exact (sortedCandidateIndices_nodup q full).idxOf_getElem position hp
  refine ⟨candidate, ⟨hmem, hcount⟩, ?_⟩
  rintro other ⟨hother, hotherCount⟩
  exact lessCount_injective q full other candidate hother hmem (hotherCount.trans hcount.symm)

/-- Writing candidate ID `i` at output slot `lessCount i` reconstructs the
original prepared support at that exact slot. -/
theorem support_at_lessCount (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (candidate : Nat) (hmem : candidate ∈ retainedCandidateIndices q full) :
    (prepareNormalization q full).order.getD (lessCount q full candidate) ∅ =
      (candidateSupports q full).getD candidate ∅ := by
  rw [← sortedCandidateSupports_eq_preparedOrder q full hq, List.getD_eq_getElem?_getD,
    List.getElem?_map, lessCount_eq_idxOf q full candidate hmem,
    List.getElem?_idxOf ((sortedCandidateIndices_perm q full).mem_iff.mpr hmem)]
  rfl

theorem existsUnique_candidate_and_support_at_position (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (position : Nat) (hposition : position < (prepareNormalization q full).indexed.nodes.size) :
    ∃! candidate, candidate ∈ retainedCandidateIndices q full ∧
      lessCount q full candidate = position ∧
      (prepareNormalization q full).order.getD position ∅ = (candidateSupports q full).getD candidate ∅ := by
  obtain ⟨candidate, ⟨hmem, hcount⟩, hunique⟩ := existsUnique_candidate_at_position q full hq position hposition
  refine ⟨candidate, ⟨hmem, hcount, ?_⟩, ?_⟩
  · rw [← hcount]
    exact support_at_lessCount q full hq candidate hmem
  · rintro other ⟨hother, hotherCount, _hsupport⟩
    exact hunique other ⟨hother, hotherCount⟩

end PaperProofs.Structure.LaminarTree.RawCandidateRankPositions
