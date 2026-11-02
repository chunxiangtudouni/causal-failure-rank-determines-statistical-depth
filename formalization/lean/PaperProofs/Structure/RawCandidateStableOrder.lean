module

public import PaperProofs.Structure.RawCandidateOrder
import all Init.Data.List.Sort.Basic

/-! The original candidate IDs determine the tie order of the prepared
node list.  The proof uses the actual stability theorem for List.mergeSort;
equal-cardinality supports need not be equal. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateStableOrder

open RawCandidateOrder

def candidateCard (q : Nat) (full : List (Finset (Fin q))) (index : Nat) : Nat :=
  ((candidateSupports q full).getD index ∅).card

def cardLE (q : Nat) (full : List (Finset (Fin q))) (left right : Nat) : Bool :=
  decide (candidateCard q full left ≤ candidateCard q full right)

/-- Compare support cardinalities first, and original candidate IDs on a
cardinality tie.  This comparison inspects only two candidates. -/
def candidateIDLE (q : Nat) (full : List (Finset (Fin q))) (left right : Nat) : Bool :=
  List.zipIdxLE (cardLE q full) (left, left) (right, right)

def sortedCandidateIndices (q : Nat) (full : List (Finset (Fin q))) : List Nat :=
  (retainedCandidateIndices q full).mergeSort (candidateIDLE q full)

theorem candidateIDLE_iff (q : Nat) (full : List (Finset (Fin q))) (left right : Nat) :
    candidateIDLE q full left right = true ↔
      candidateCard q full left < candidateCard q full right ∨
        candidateCard q full left = candidateCard q full right ∧ left ≤ right := by
  simp only [candidateIDLE, List.zipIdxLE, cardLE]
  by_cases hleft : candidateCard q full left ≤ candidateCard q full right
  · by_cases hright : candidateCard q full right ≤ candidateCard q full left
    · simp [hleft, hright]
      omega
    · simp [hleft, hright]
      omega
  · simp [hleft]
    omega

theorem retainedCandidateIndices_pairwise_lt (q : Nat) (full : List (Finset (Fin q))) :
    (retainedCandidateIndices q full).Pairwise (· < ·) := by
  exact List.pairwise_lt_range.filter _

/-- The retained enumeration has gaps, but its position order is exactly
the original candidate-ID order. -/
theorem retained_zipIdx_le_iff (q : Nat) (full : List (Finset (Fin q)))
    (left right : Nat × Nat)
    (hleft : left ∈ (retainedCandidateIndices q full).zipIdx)
    (hright : right ∈ (retainedCandidateIndices q full).zipIdx) :
    left.2 ≤ right.2 ↔ left.1 ≤ right.1 := by
  have hl := List.snd_lt_of_mem_zipIdx hleft
  have hr := List.snd_lt_of_mem_zipIdx hright
  simp only [Nat.add_zero] at hl hr
  have hel := List.fst_eq_of_mem_zipIdx hleft
  have her := List.fst_eq_of_mem_zipIdx hright
  simp only [Nat.sub_zero, List.getElem_eq_getD 0] at hel her
  have hsorted := retainedCandidateIndices_pairwise_lt q full
  by_cases hlt : left.2 < right.2
  · have hids := hsorted.rel_getElem_of_lt hl hr hlt
    simp only [List.getElem_eq_getD 0] at hids
    rw [← hel, ← her] at hids
    omega
  · by_cases heq : left.2 = right.2
    · have hids : left.1 = right.1 := by rw [hel, her, heq]
      omega
    · have hgt : right.2 < left.2 := by omega
      have hids := hsorted.rel_getElem_of_lt hr hl hgt
      simp only [List.getElem_eq_getD 0] at hids
      rw [← hel, ← her] at hids
      omega

theorem zipIdx_comparator_eq_candidateIDLE (q : Nat) (full : List (Finset (Fin q)))
    (left right : Nat × Nat)
    (hleft : left ∈ (retainedCandidateIndices q full).zipIdx)
    (hright : right ∈ (retainedCandidateIndices q full).zipIdx) :
    List.zipIdxLE (cardLE q full) left right = candidateIDLE q full left.1 right.1 := by
  have hpositions := retained_zipIdx_le_iff q full left right hleft hright
  simp only [candidateIDLE, List.zipIdxLE]
  by_cases hab : cardLE q full left.1 right.1 = true
  · by_cases hba : cardLE q full right.1 left.1 = true
    · simp only [hab, hba, ite_true]
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using hpositions
    · simp [hab, hba]
  · simp [hab]

/-- Explicit original-ID tie breaking has the same output as the original
stable cardinality sort, because the input IDs are strictly increasing. -/
theorem sortedCandidateIndices_eq_card_sort (q : Nat) (full : List (Finset (Fin q))) :
    sortedCandidateIndices q full =
      (retainedCandidateIndices q full).mergeSort (cardLE q full) := by
  have htransport := List.map_mergeSort
    (r := List.zipIdxLE (cardLE q full)) (s := candidateIDLE q full)
    (f := Prod.fst) (l := (retainedCandidateIndices q full).zipIdx)
    (fun left hleft right hright =>
      zipIdx_comparator_eq_candidateIDLE q full left right hleft hright)
  rw [List.zipIdx_map_fst] at htransport
  change (retainedCandidateIndices q full).mergeSort (candidateIDLE q full) = _
  rw [← htransport]
  exact List.mergeSort_zipIdx

/-- This equality identifies every output position, including ties, with
the frozen prepared order.  No sorted node answer is supplied to ROM. -/
theorem sortedCandidateSupports_eq_preparedOrder (q : Nat)
    (full : List (Finset (Fin q))) (hq : 0 < q) :
    (sortedCandidateIndices q full).map
      (fun index => (candidateSupports q full).getD index ∅) =
        (prepareNormalization q full).order := by
  rw [sortedCandidateIndices_eq_card_sort]
  have htransport := List.map_mergeSort (r := cardLE q full)
    (s := fun left right : Finset (Fin q) => decide (left.card ≤ right.card))
    (f := fun index => (candidateSupports q full).getD index ∅)
    (l := retainedCandidateIndices q full) (fun _ _ _ _ => rfl)
  exact htransport.trans (retainedCandidateSupports_mergeSort q full hq)

theorem sortedCandidateIndices_perm (q : Nat) (full : List (Finset (Fin q))) :
    (sortedCandidateIndices q full).Perm (retainedCandidateIndices q full) :=
  List.mergeSort_perm _ _

theorem sortedCandidateIndices_pairwise (q : Nat) (full : List (Finset (Fin q))) :
    (sortedCandidateIndices q full).Pairwise (fun left right =>
      candidateCard q full left < candidateCard q full right ∨
        candidateCard q full left = candidateCard q full right ∧ left ≤ right) := by
  have htrans : ∀ a b c, candidateIDLE q full a b → candidateIDLE q full b c →
      candidateIDLE q full a c := by
    intro a b c hab hbc
    rw [candidateIDLE_iff] at hab hbc ⊢
    omega
  have htotal : ∀ a b, candidateIDLE q full a b || candidateIDLE q full b a := by
    intro a b
    simp only [Bool.or_eq_true, candidateIDLE_iff]
    omega
  exact (List.pairwise_mergeSort htrans htotal (retainedCandidateIndices q full)).imp
    (fun {_ _} h => (candidateIDLE_iff q full _ _).mp h)

end PaperProofs.Structure.LaminarTree.RawCandidateStableOrder
