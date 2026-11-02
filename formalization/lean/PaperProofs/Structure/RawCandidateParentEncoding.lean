module

public import PaperProofs.Structure.RawCandidateParentScan
public import PaperProofs.Structure.RawCandidateRankPositions
public import PaperProofs.Structure.IndexedClosureRAM

/-! The parent scan's actual retained raw ID is encoded by its proved
stable position plus one.  Agreement is required of a runtime inverse
dictionary only at retained IDs; nonretained entries supply no parent. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentEncoding

open RawCandidateOrder RawCandidateParents RawCandidateRankPositions RawCandidateParentScan
  IndexedClosureRAM

theorem findNodeId_eq_some_lessCount (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (candidate : Nat) (hmem : candidate ∈ retainedCandidateIndices q full) :
    findNodeId (prepareNormalization q full).indexed.nodes (candidateSupport q full candidate) =
      some ⟨lessCount q full candidate, lessCount_lt_size q full hq candidate hmem⟩ := by
  have hnodup : (prepareNormalization q full).indexed.nodes.toList.Nodup := by
    simpa only [NormalizationData.indexed, indexNodes, List.toList_toArray] using prepared_order_nodup q full
  apply (findNodeId_eq_some_iff _ hnodup _ _).mpr
  have hpos : lessCount q full candidate < (prepareNormalization q full).order.length := by
    have h := lessCount_lt_size q full hq candidate hmem
    change lessCount q full candidate < (prepareNormalization q full).order.toArray.size at h
    simpa only [List.size_toArray] using h
  have hsupport := support_at_lessCount q full hq candidate hmem
  rw [List.getD_eq_getElem _ ∅ hpos] at hsupport
  change (prepareNormalization q full).order.toArray[lessCount q full candidate] = _
  simpa only [List.getElem_toArray, candidateSupport] using hsupport

theorem encoded_findNodeId_eq_lessCount_add_one (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (candidate : Nat) (hmem : candidate ∈ retainedCandidateIndices q full) :
    encodedNode (prepareNormalization q full).indexed
      (findNodeId (prepareNormalization q full).indexed.nodes (candidateSupport q full candidate)) =
        lessCount q full candidate + 1 := by
  rw [findNodeId_eq_some_lessCount q full hq candidate hmem]
  rfl

/-- The finite parent selection itself supplies the retained-ID premise;
the original indexed parent is a conclusion, never an input oracle. -/
theorem parentCandidate_rankEncoding (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (child : (prepareNormalization q full).indexed.NodeId) (candidate : Nat)
    (hchild : candidateSupport q full candidate = (prepareNormalization q full).indexed.decode child) :
    ((parentCandidate q full candidate).map (fun parent => lessCount q full parent + 1)).getD 0 =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child) := by
  have hbind := parentCandidate_bind_findNodeId q full hq child candidate hchild
  have hencoded := congrArg (encodedNode (prepareNormalization q full).indexed) hbind
  cases hpick : parentCandidate q full candidate with
  | none => simpa only [hpick, Option.bind_none, Option.map_none, Option.getD_none, encodedNode] using hencoded
  | some parent =>
    have hmem := (parentCandidate_mem q full candidate parent hpick).1
    have hfind := findNodeId_eq_some_lessCount q full hq parent hmem
    simpa only [hpick, Option.bind_some, hfind, encodedNode, Option.map_some, Option.getD_some] using hencoded

theorem parentCandidate_encoding_of_inverse (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (inverse : Nat → Nat)
    (hinverse : ∀ parent ∈ retainedCandidateIndices q full, inverse parent = lessCount q full parent + 1)
    (child : (prepareNormalization q full).indexed.NodeId) (candidate : Nat)
    (hchild : candidateSupport q full candidate = (prepareNormalization q full).indexed.decode child) :
    ((parentCandidate q full candidate).map inverse).getD 0 =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child) := by
  have hrank := parentCandidate_rankEncoding q full hq child candidate hchild
  cases hpick : parentCandidate q full candidate with
  | none => simpa only [hpick, Option.map_none, Option.getD_none] using hrank
  | some parent =>
    have hvalue := hinverse parent (parentCandidate_mem q full candidate parent hpick).1
    simpa only [hpick, Option.map_some, Option.getD_some, hvalue] using hrank

theorem bestEncoded_full_of_inverse (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (inverse : Nat → Nat)
    (hinverse : ∀ parent ∈ retainedCandidateIndices q full, inverse parent = lessCount q full parent + 1)
    (child : (prepareNormalization q full).indexed.NodeId) (candidate : Nat)
    (hchild : candidateSupport q full candidate = (prepareNormalization q full).indexed.decode child) :
    bestEncoded q full inverse candidate (full.length + q + 1) =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child) := by
  unfold bestEncoded
  rw [choice_full]
  exact parentCandidate_encoding_of_inverse q full hq inverse hinverse child candidate hchild

/-- The actual ordering table stores zero on nonretained IDs. -/
def retainedInverse (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) : Nat :=
  if keepCandidate q full candidate then lessCount q full candidate + 1 else 0

theorem retainedInverse_of_mem (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat)
    (hmem : candidate ∈ retainedCandidateIndices q full) :
    retainedInverse q full candidate = lessCount q full candidate + 1 := by
  have hkeep := ((retainedCandidateIndices_mem_iff q full candidate).mp hmem).2
  simp only [retainedInverse, hkeep, ite_true]

theorem bestEncoded_full (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (child : (prepareNormalization q full).indexed.NodeId) (candidate : Nat)
    (hchild : candidateSupport q full candidate = (prepareNormalization q full).indexed.decode child) :
    bestEncoded q full (retainedInverse q full) candidate (full.length + q + 1) =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child) :=
  bestEncoded_full_of_inverse q full hq (retainedInverse q full)
    (fun parent hmem => retainedInverse_of_mem q full parent hmem) child candidate hchild

end PaperProofs.Structure.LaminarTree.RawCandidateParentEncoding
