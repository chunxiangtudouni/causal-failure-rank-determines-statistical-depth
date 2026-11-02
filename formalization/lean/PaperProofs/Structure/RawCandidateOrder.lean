module

public import PaperProofs.Structure.LaminarNormalize
import Mathlib.Data.List.Range

/-! Exact candidate order for the raw inclusion-tree construction.  The
original list deduplication retains the last occurrence, including ties
between the root, input stages, and the final singleton candidates. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateOrder

/-- The raw enumeration before any filtering or equality tests. -/
def candidateSupports (q : Nat) (full : List (Finset (Fin q))) : List (Finset (Fin q)) :=
  Finset.univ :: (full ++ List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q))))

/-- Retain a nonempty support exactly at its last position.  Both tests are
finite and executable; the suffix test inspects only later candidates. -/
def keepSupport {q : Nat} (supports : List (Finset (Fin q))) (index : Nat) : Bool :=
  decide ((supports.getD index ∅).Nonempty ∧
    supports.getD index ∅ ∉ supports.drop (index + 1))

def retainedIndices {q : Nat} (supports : List (Finset (Fin q))) : List Nat :=
  (List.range supports.length).filter (keepSupport supports)

def retainedSupports {q : Nat} (supports : List (Finset (Fin q))) : List (Finset (Fin q)) :=
  (retainedIndices supports).map (fun index => supports.getD index ∅)

def keepCandidate (q : Nat) (full : List (Finset (Fin q))) (index : Nat) : Bool :=
  keepSupport (candidateSupports q full) index

def retainedCandidateIndices (q : Nat) (full : List (Finset (Fin q))) : List Nat :=
  retainedIndices (candidateSupports q full)

@[simp] theorem candidateSupports_length (q : Nat) (full : List (Finset (Fin q))) :
    (candidateSupports q full).length = full.length + q + 1 := by
  simp [candidateSupports]

@[simp] theorem keepSupport_cons_zero {q : Nat} (head : Finset (Fin q))
    (tail : List (Finset (Fin q))) :
    keepSupport (head :: tail) 0 = decide (head.Nonempty ∧ head ∉ tail) := by
  simp [keepSupport]

@[simp] theorem keepSupport_cons_succ {q : Nat} (head : Finset (Fin q))
    (tail : List (Finset (Fin q))) (index : Nat) :
    keepSupport (head :: tail) (index + 1) = keepSupport tail index := by
  simp [keepSupport]

theorem retainedSupports_cons {q : Nat} (head : Finset (Fin q))
    (tail : List (Finset (Fin q))) :
    retainedSupports (head :: tail) =
      if head.Nonempty ∧ head ∉ tail then head :: retainedSupports tail
      else retainedSupports tail := by
  simp only [retainedSupports, retainedIndices, List.length_cons, List.range_succ_eq_map,
    List.filter_cons, keepSupport_cons_zero, List.filter_map]
  have hshift : keepSupport (head :: tail) ∘ Nat.succ = keepSupport tail := by
    funext index
    exact keepSupport_cons_succ head tail index
  rw [hshift]
  by_cases h : head.Nonempty ∧ head ∉ tail
  · simp [h, List.map_map, Function.comp_def]
  · simp [h, List.map_map, Function.comp_def]

/-- This is an equality of lists, proved from the actual right-retaining
`List.dedup_cons` equations rather than from equality of node families. -/
theorem retainedSupports_eq_filter_dedup {q : Nat} (supports : List (Finset (Fin q))) :
    retainedSupports supports =
      (supports.filter (fun support => decide support.Nonempty)).dedup := by
  induction supports with
  | nil => simp [retainedSupports, retainedIndices]
  | cons head tail ih =>
    rw [retainedSupports_cons]
    by_cases hnonempty : head.Nonempty
    · have hmem : head ∈ tail.filter (fun support => decide support.Nonempty) ↔ head ∈ tail := by
        simp [hnonempty]
      by_cases hlater : head ∈ tail
      · simp [hnonempty, hlater, ih, List.dedup_cons_of_mem (hmem.mpr hlater)]
      · simp [hnonempty, hlater, ih, List.dedup_cons_of_notMem (hmem.not.mpr hlater)]
    · simp [hnonempty, ih]

theorem candidateSupports_filter_nonempty (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (candidateSupports q full).filter (fun support => decide support.Nonempty) =
      Finset.univ :: (full.filter (fun support => decide support.Nonempty) ++
        List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q)))) := by
  have hroot : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hsingletons :
      (List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q)))).filter
        (fun support => decide support.Nonempty) =
      List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q))) := by
    apply List.filter_eq_self.mpr
    intro support hsupport
    obtain ⟨tool, rfl⟩ := List.mem_ofFn.mp hsupport
    simp
  simp only [candidateSupports, List.filter_cons, hroot, decide_true, ite_true,
    List.filter_append, hsingletons]

theorem retainedCandidateSupports_eq_explicitNodeList (q : Nat)
    (full : List (Finset (Fin q))) (hq : 0 < q) :
    (retainedCandidateIndices q full).map
      (fun index => (candidateSupports q full).getD index ∅) = explicitNodeList q full := by
  change retainedSupports (candidateSupports q full) = _
  rw [retainedSupports_eq_filter_dedup, candidateSupports_filter_nonempty q full hq]
  rfl

theorem retainedCandidateIndices_mem_iff (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    index ∈ retainedCandidateIndices q full ↔
      index < full.length + q + 1 ∧ keepCandidate q full index = true := by
  simp [retainedCandidateIndices, retainedIndices, keepCandidate]

theorem keepSupport_iff_no_later_index {q : Nat} (supports : List (Finset (Fin q))) (index : Nat) :
    keepSupport supports index = true ↔
      (supports.getD index ∅).Nonempty ∧
        ∀ later, index < later → later < supports.length →
          supports.getD later ∅ ≠ supports.getD index ∅ := by
  simp only [keepSupport, decide_eq_true_eq]
  apply and_congr_right
  intro _
  constructor
  · intro hnone later hlater hbound hequal
    apply hnone
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨later - (index + 1), by omega, ?_⟩
    have heq : index + 1 + (later - (index + 1)) = later := by omega
    simpa only [heq, List.getElem_eq_getD ∅] using hequal
  · intro hnone hmem
    obtain ⟨offset, hbound, hequal⟩ := List.mem_drop_iff_getElem.mp hmem
    apply hnone (index + 1 + offset) (by omega) (by omega)
    simpa only [List.getElem_eq_getD ∅] using hequal

theorem keepCandidate_iff_no_later_index (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    keepCandidate q full index = true ↔
      ((candidateSupports q full).getD index ∅).Nonempty ∧
        ∀ later, index < later → later < full.length + q + 1 →
          (candidateSupports q full).getD later ∅ ≠ (candidateSupports q full).getD index ∅ := by
  simpa only [keepCandidate, candidateSupports_length] using
    keepSupport_iff_no_later_index (candidateSupports q full) index

/-- Sorting exactly the retained list recovers the original prepared order,
including its original tie handling.  No antisymmetry of cardinality on
different supports is used. -/
theorem retainedCandidateSupports_mergeSort (q : Nat)
    (full : List (Finset (Fin q))) (hq : 0 < q) :
    ((retainedCandidateIndices q full).map
      (fun index => (candidateSupports q full).getD index ∅)).mergeSort
        (fun left right => decide (left.card ≤ right.card)) =
      (prepareNormalization q full).order := by
  rw [retainedCandidateSupports_eq_explicitNodeList q full hq]
  rfl

end PaperProofs.Structure.LaminarTree.RawCandidateOrder
