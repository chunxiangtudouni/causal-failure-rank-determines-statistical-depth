module

public import PaperProofs.Structure.RawCandidateStableOrder
public import PaperProofs.Structure.IndexedNodeCache

/-! Parent search over the actual retained raw candidate IDs.  The search
filters strict supersets and scans for the least cardinality using the
existing executable List.argmin.  No machine or operation bound is claimed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateParents

open RawCandidateOrder RawCandidateStableOrder

def candidateSupport (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) : Finset (Fin q) :=
  (candidateSupports q full).getD candidate ∅

def parentCandidates (q : Nat) (full : List (Finset (Fin q))) (child : Nat) : List Nat :=
  (retainedCandidateIndices q full).filter
    (fun parent => decide (candidateSupport q full child ⊂ candidateSupport q full parent))

def parentCandidate (q : Nat) (full : List (Finset (Fin q))) (child : Nat) : Option Nat :=
  List.argmin (candidateCard q full) (parentCandidates q full child)

private theorem map_argmin_support (q : Nat) (full : List (Finset (Fin q))) (ids : List Nat) :
    (List.argmin (candidateCard q full) ids).map (candidateSupport q full) =
      List.argmin Finset.card (ids.map (candidateSupport q full)) := by
  induction ids with
  | nil => rfl
  | cons first tail ih =>
    rw [List.argmin_cons, List.map_cons, List.argmin_cons, ← ih]
    cases htail : List.argmin (candidateCard q full) tail with
    | none => rfl
    | some best =>
      simp only [Option.map_some]
      change (if candidateCard q full best < candidateCard q full first then
        some best else some first).map (candidateSupport q full) =
          if candidateCard q full best < candidateCard q full first then
            some (candidateSupport q full best) else some (candidateSupport q full first)
      by_cases hbetter : candidateCard q full best < candidateCard q full first
      · simp only [hbetter, ite_true, Option.map_some]
      · simp only [hbetter, ite_false, Option.map_some]

theorem parentCandidates_supports (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (child : Nat) :
    (parentCandidates q full child).map (candidateSupport q full) =
      (explicitNodeList q full).filter
        (fun parent => decide (candidateSupport q full child ⊂ parent)) := by
  have hretained : (retainedCandidateIndices q full).map (candidateSupport q full) =
      explicitNodeList q full := retainedCandidateSupports_eq_explicitNodeList q full hq
  rw [← hretained, List.filter_map]
  rfl

/-- Exact list-order transport to the original parent search.  No
laminarity or assumed parent correctness is needed for this identity. -/
theorem parentCandidate_map_eq_explicitParent (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (child : Nat) :
    (parentCandidate q full child).map (candidateSupport q full) =
      explicitParent q full (candidateSupport q full child) := by
  rw [parentCandidate, map_argmin_support, parentCandidates_supports q full hq]
  rfl

theorem retained_support_mem_nodeFamily (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (child : Nat) (hchild : child ∈ retainedCandidateIndices q full) :
    candidateSupport q full child ∈ nodeFamily full := by
  have hmem : candidateSupport q full child ∈ explicitNodeList q full := by
    rw [← retainedCandidateSupports_eq_explicitNodeList q full hq]
    exact List.mem_map_of_mem hchild
  simpa only [explicitNodeList_toFinset] using List.mem_toFinset.mpr hmem

theorem retained_support_nonempty (q : Nat) (full : List (Finset (Fin q)))
    (child : Nat) (hchild : child ∈ retainedCandidateIndices q full) :
    (candidateSupport q full child).Nonempty := by
  have hkeep := (retainedCandidateIndices_mem_iff q full child).mp hchild
  exact ((keepCandidate_iff_no_later_index q full child).mp hkeep.2).1

/-- Retaining the final occurrence gives an injective map from retained
raw IDs to supports, even when the original stage list has repetitions. -/
theorem retained_support_injective (q : Nat) (full : List (Finset (Fin q)))
    (left right : Nat) (hleft : left ∈ retainedCandidateIndices q full)
    (hright : right ∈ retainedCandidateIndices q full)
    (heq : candidateSupport q full left = candidateSupport q full right) : left = right := by
  obtain ⟨hleftBound, hleftKeep⟩ := (retainedCandidateIndices_mem_iff q full left).mp hleft
  obtain ⟨hrightBound, hrightKeep⟩ := (retainedCandidateIndices_mem_iff q full right).mp hright
  have hlater := ((keepCandidate_iff_no_later_index q full left).mp hleftKeep).2
  have hrater := ((keepCandidate_iff_no_later_index q full right).mp hrightKeep).2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hlater right hlt hrightBound heq.symm
  · exact hrater left hgt hleftBound heq

theorem parentCandidate_mem (q : Nat) (full : List (Finset (Fin q))) (child parent : Nat)
    (hpick : parentCandidate q full child = some parent) :
    parent ∈ retainedCandidateIndices q full ∧
      candidateSupport q full child ⊂ candidateSupport q full parent := by
  have hmem := List.argmin_mem hpick
  have hfields := List.mem_filter.mp hmem
  exact ⟨hfields.1, by simpa only [decide_eq_true_eq] using hfields.2⟩

theorem parentCandidate_card_min (q : Nat) (full : List (Finset (Fin q)))
    (child parent : Nat) (hpick : parentCandidate q full child = some parent)
    (other : Nat) (hother : other ∈ retainedCandidateIndices q full)
    (hstrict : candidateSupport q full child ⊂ candidateSupport q full other) :
    candidateCard q full parent ≤ candidateCard q full other := by
  exact List.le_of_mem_argmin (List.mem_filter.mpr ⟨hother, by simp only [hstrict, decide_true]⟩) hpick

theorem parentCandidate_isParent (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (child parent : Nat)
    (hchild : child ∈ retainedCandidateIndices q full)
    (hpick : parentCandidate q full child = some parent) :
    IsParent (nodeFamily full) (candidateSupport q full child) (candidateSupport q full parent) := by
  have hmapped := parentCandidate_map_eq_explicitParent q full hq child
  rw [hpick, Option.map_some] at hmapped
  exact parentFromList_isParent (explicitNodeList q full) (explicitNodeList_toFinset q full)
    (nodeFamily_laminar full hlaminar) (retained_support_nonempty q full child hchild) hmapped.symm

/-- The root may occur at a later retained ID (for example q=1); its
support, rather than an assumed raw ID zero, determines the absent parent. -/
theorem parentCandidate_root_none (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (child : Nat) (hroot : candidateSupport q full child = Finset.univ) :
    parentCandidate q full child = none := by
  have hmapped := parentCandidate_map_eq_explicitParent q full hq child
  rw [hroot] at hmapped
  change (parentCandidate q full child).map (candidateSupport q full) =
    parentFromList (explicitNodeList q full) Finset.univ at hmapped
  rw [parentFromList_root_none] at hmapped
  cases hparent : parentCandidate q full child with
  | none => rfl
  | some parent => simp only [hparent, Option.map_some, reduceCtorEq] at hmapped

theorem parentCandidate_exists (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (child : Nat)
    (hchild : child ∈ retainedCandidateIndices q full)
    (hroot : candidateSupport q full child ≠ Finset.univ) :
    ∃ parent, parentCandidate q full child = some parent ∧
      parent ∈ retainedCandidateIndices q full ∧
      IsParent (nodeFamily full) (candidateSupport q full child) (candidateSupport q full parent) := by
  obtain ⟨support, hparent, _hproper⟩ := explicitParent_spec q full hq hlaminar
    (retained_support_mem_nodeFamily q full hq child hchild) hroot
  have hmapped := parentCandidate_map_eq_explicitParent q full hq child
  rw [hparent] at hmapped
  cases hpick : parentCandidate q full child with
  | none => simp only [hpick, Option.map_none, reduceCtorEq] at hmapped
  | some parent => exact ⟨parent, rfl, (parentCandidate_mem q full child parent hpick).1,
      parentCandidate_isParent q full hq hlaminar child parent hchild hpick⟩

/-- Genuine laminar parents are unique as supports, and retained IDs are
injective.  Hence equal-cardinality parent candidates cannot create an
extra tie choice for the original tree. -/
theorem parentCandidate_card_tie_unique (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (child parent other : Nat)
    (hchild : child ∈ retainedCandidateIndices q full)
    (hpick : parentCandidate q full child = some parent)
    (hother : other ∈ retainedCandidateIndices q full)
    (hstrict : candidateSupport q full child ⊂ candidateSupport q full other)
    (hcard : candidateCard q full other = candidateCard q full parent) : other = parent := by
  have hparent := parentCandidate_isParent q full hq hlaminar child parent hchild hpick
  have hotherFamily := retained_support_mem_nodeFamily q full hq other hother
  have hsub := hparent.2.2 _ hotherFamily hstrict
  have hsupport : candidateSupport q full other = candidateSupport q full parent :=
    (Finset.eq_of_subset_of_card_le hsub (by simpa only [candidateCard, candidateSupport] using hcard.le)).symm
  exact retained_support_injective q full other parent hother
    (parentCandidate_mem q full child parent hpick).1 hsupport

/-- Translate the scanned raw parent ID using the existing support-to-ID
lookup.  The result is exactly the original prepared indexed parent; the
equation does not assume any parent value or machine performance. -/
theorem parentCandidate_bind_findNodeId (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (child : (prepareNormalization q full).indexed.NodeId) (candidate : Nat)
    (hchild : candidateSupport q full candidate = (prepareNormalization q full).indexed.decode child) :
    (parentCandidate q full candidate).bind (fun parent =>
      findNodeId (prepareNormalization q full).indexed.nodes (candidateSupport q full parent)) =
        (prepareNormalization q full).indexed.parents.get child := by
  rw [show (prepareNormalization q full).indexed.parents.get child =
    ((prepareNormalization q full).parentSupport ((prepareNormalization q full).indexed.decode child)).bind
      (findNodeId (prepareNormalization q full).indexed.nodes) from indexNodes_parent_get _ _ child]
  rw [prepared_parentSupport q full _ (prepared_indexed_node_mem q full child), ← hchild,
    ← parentCandidate_map_eq_explicitParent q full hq candidate]
  cases parentCandidate q full candidate <;> rfl

end PaperProofs.Structure.LaminarTree.RawCandidateParents
