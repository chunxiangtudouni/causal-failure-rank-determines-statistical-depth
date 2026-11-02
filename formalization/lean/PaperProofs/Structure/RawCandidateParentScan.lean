module

public import PaperProofs.Structure.RawCandidateParents

/-! Partial argmin invariant for scanning the retained raw parent candidates.
The absent-choice score is q+1, strictly above every actual support card.
Only strict improvement replaces a choice, preserving the original first
tie convention of List.argmin.  No machine implementation is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentScan

open RawCandidateOrder RawCandidateStableOrder RawCandidateParents

def eligible (q : Nat) (full : List (Finset (Fin q))) (child parent : Nat) : Bool :=
  keepCandidate q full parent &&
    decide (candidateSupport q full child ⊂ candidateSupport q full parent)

def choice (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) : Option Nat :=
  List.argmin (candidateCard q full) ((List.range upto).filter (eligible q full child))

def bestCard (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) : Nat :=
  ((choice q full child upto).map (candidateCard q full)).getD (q + 1)

def bestEncoded (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat)
    (child upto : Nat) : Nat := ((choice q full child upto).map inverse).getD 0

theorem candidateCard_le_q (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) :
    candidateCard q full candidate ≤ q := by
  simpa only [candidateCard, Fintype.card_fin] using
    Finset.card_le_univ ((candidateSupports q full).getD candidate ∅)

theorem choice_zero (q : Nat) (full : List (Finset (Fin q))) (child : Nat) :
    choice q full child 0 = none := rfl

theorem bestCard_zero (q : Nat) (full : List (Finset (Fin q))) (child : Nat) :
    bestCard q full child 0 = q + 1 := rfl

theorem bestEncoded_zero (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat) (child : Nat) :
    bestEncoded q full inverse child 0 = 0 := rfl

private theorem choice_succ_raw (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) :
    choice q full child (upto + 1) =
      if eligible q full child upto then
        match choice q full child upto with
        | none => some upto
        | some best => if candidateCard q full upto < candidateCard q full best then some upto else some best
      else choice q full child upto := by
  unfold choice
  rw [List.range_succ, List.filter_append]
  cases hkeep : eligible q full child upto
  · simp only [List.filter_cons, hkeep, Bool.false_eq_true, ite_false, List.filter_nil, List.append_nil]
  · simp only [List.filter_cons, hkeep, ite_true, List.filter_nil]
    rw [List.argmin_concat]
    cases List.argmin (candidateCard q full) ((List.range upto).filter (eligible q full child)) <;> rfl

theorem choice_succ (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) :
    choice q full child (upto + 1) =
      if eligible q full child upto && decide (candidateCard q full upto < bestCard q full child upto)
      then some upto else choice q full child upto := by
  rw [choice_succ_raw]
  have hsentinel : candidateCard q full upto < q + 1 := by
    have hcard := candidateCard_le_q q full upto
    omega
  cases hkeep : eligible q full child upto <;> cases hchoice : choice q full child upto <;>
    simp [hchoice, bestCard, hsentinel]

theorem bestCard_succ (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat) :
    bestCard q full child (upto + 1) =
      if eligible q full child upto && decide (candidateCard q full upto < bestCard q full child upto)
      then candidateCard q full upto else bestCard q full child upto := by
  change ((choice q full child (upto + 1)).map (candidateCard q full)).getD (q + 1) = _
  rw [choice_succ]
  cases eligible q full child upto && decide (candidateCard q full upto < bestCard q full child upto) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Option.map_some, Option.getD_some, bestCard]

theorem bestEncoded_succ (q : Nat) (full : List (Finset (Fin q))) (inverse : Nat → Nat)
    (child upto : Nat) :
    bestEncoded q full inverse child (upto + 1) =
      if eligible q full child upto && decide (candidateCard q full upto < bestCard q full child upto)
      then inverse upto else bestEncoded q full inverse child upto := by
  change ((choice q full child (upto + 1)).map inverse).getD 0 = _
  rw [choice_succ]
  cases eligible q full child upto && decide (candidateCard q full upto < bestCard q full child upto) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Option.map_some, Option.getD_some, bestEncoded]

theorem choice_preserves_card_tie (q : Nat) (full : List (Finset (Fin q))) (child upto : Nat)
    (htie : candidateCard q full upto = bestCard q full child upto) :
    choice q full child (upto + 1) = choice q full child upto := by
  rw [choice_succ]
  simp only [htie, Nat.lt_irrefl, decide_false, Bool.and_false, Bool.false_eq_true, ite_false]

theorem choice_full (q : Nat) (full : List (Finset (Fin q))) (child : Nat) :
    choice q full child (full.length + q + 1) = parentCandidate q full child := by
  simp only [choice, parentCandidate, parentCandidates, retainedCandidateIndices, retainedIndices,
    candidateSupports_length, List.filter_filter]
  unfold eligible
  simp only [keepCandidate, Bool.and_comm]

/-- The actual directed-difference counters detect strict supersets. -/
theorem strictSubset_iff_differenceCounts {q : Nat} (left right : Finset (Fin q)) :
    left ⊂ right ↔ (left \ right).card = 0 ∧ 0 < (right \ left).card := by
  simp only [Nat.pos_iff_ne_zero, ne_eq, Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset]
  exact lt_iff_le_not_ge

end PaperProofs.Structure.LaminarTree.RawCandidateParentScan
