module

public import PaperProofs.Structure.RawCandidateRankPositions
public import PaperProofs.Structure.AlgorithmClaims

/-! Partial counts for scanning every raw candidate ID.  No retention
assumption on the queried ID is needed: its own contribution is always
zero, so even a nonretained ID has a final rank below the M-slot bound. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateRankScan

open RawCandidateOrder RawCandidateRankPositions AlgorithmClaims

def rankBefore (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) : Nat :=
  ((List.range upto).filter
    (fun other => keepCandidate q full other && decide (Precedes q full other index))).length

theorem rankBefore_zero (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    rankBefore q full index 0 = 0 := rfl

theorem rankBefore_succ (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) :
    rankBefore q full index (upto + 1) = rankBefore q full index upto +
      bit (keepCandidate q full upto && decide (Precedes q full upto index)) := by
  simp only [rankBefore, List.range_succ, List.filter_append, List.length_append,
    List.filter_cons, List.filter_nil]
  cases keepCandidate q full upto && decide (Precedes q full upto index) <;> simp [bit]

theorem rankBefore_full (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    rankBefore q full index (full.length + q + 1) = lessCount q full index := by
  simp only [rankBefore, lessCount, retainedCandidateIndices, retainedIndices,
    candidateSupports_length, List.filter_filter, keepCandidate, Bool.and_comm]

theorem rankBefore_le (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat) :
    rankBefore q full index upto ≤ upto := by
  simpa only [rankBefore, List.length_range] using List.length_filter_le
    (fun other => keepCandidate q full other && decide (Precedes q full other index)) (List.range upto)

theorem rankBefore_lt_of_self (q : Nat) (full : List (Finset (Fin q))) (index upto : Nat)
    (hindex : index < upto) : rankBefore q full index upto < upto := by
  have hshort : ((List.range upto).filter
      (fun other => keepCandidate q full other && decide (Precedes q full other index))).length <
        (List.range upto).length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    refine ⟨index, List.mem_range.mpr hindex, ?_⟩
    simp [Precedes]
  simpa only [rankBefore, List.length_range] using hshort

theorem rankBefore_full_lt (q : Nat) (full : List (Finset (Fin q))) (index : Nat)
    (hindex : index < full.length + q + 1) :
    rankBefore q full index (full.length + q + 1) < full.length + q + 1 :=
  rankBefore_lt_of_self q full index _ hindex

theorem lessCount_lt_candidateCount (q : Nat) (full : List (Finset (Fin q))) (index : Nat)
    (hindex : index < full.length + q + 1) : lessCount q full index < full.length + q + 1 := by
  rw [← rankBefore_full]
  exact rankBefore_full_lt q full index hindex

end PaperProofs.Structure.LaminarTree.RawCandidateRankScan
