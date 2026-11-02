module

public import PaperProofs.Structure.RawTreeSerialization

/-! Recover the original ordered children arrays from encoded parent words.
Both the parent and child scans use ascending IDs.  Equalities below are
of actual lists, including their order, rather than only node families. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateChildrenLayout

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims RawTreeSerialization

def childIDs (size : Nat) (parentWords : Nat → Nat) (parent : Nat) : List Nat :=
  (List.range size).filter (fun child => decide (parentWords child = parent + 1))

def flatChildren (size : Nat) (parentWords : Nat → Nat) : List Nat :=
  (List.range size).flatMap (childIDs size parentWords)

private theorem finRange_map_val (size : Nat) : (List.finRange size).map Fin.val = List.range size := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range]
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    rfl

private theorem prepared_children_toList (q : Nat) (full : List (Finset (Fin q)))
    (parent : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.children.get parent).toList =
      (List.finRange (prepareNormalization q full).indexed.nodes.size).filter
        (fun child => decide ((prepareNormalization q full).indexed.parents.get child = some parent)) := by
  change ((Vector.ofFn (fun selected : (prepareNormalization q full).indexed.NodeId =>
    ((List.finRange (prepareNormalization q full).indexed.nodes.size).filter
      (fun child => decide ((prepareNormalization q full).indexed.parents.get child = some selected))).toArray)).get parent).toList = _
  rw [cache_get_ofFn, List.toList_toArray]

section ParentWords

variable (q : Nat) (full : List (Finset (Fin q))) (parentWords : Nat → Nat)
  (hwords : ∀ child (hchild : child < (prepareNormalization q full).indexed.nodes.size),
    parentWords child = encodedNode (prepareNormalization q full).indexed
      ((prepareNormalization q full).indexed.parents.get ⟨child, hchild⟩))

include hwords

/-- Only encoded parent words are the input protocol; the ordered child
list follows from the original indexNodes construction. -/
theorem childIDs_eq_prepared (parent : (prepareNormalization q full).indexed.NodeId) :
    childIDs (prepareNormalization q full).indexed.nodes.size parentWords parent.val =
      ((prepareNormalization q full).indexed.children.get parent).toList.map Fin.val := by
  rw [childIDs, ← finRange_map_val, List.filter_map, prepared_children_toList]
  apply congrArg (List.map Fin.val)
  apply List.filter_congr
  intro child _hchild
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, hwords child.val child.isLt,
    UniformNormalizationRAM.encodedNode_eq_some]

theorem childIDs_length_eq_degree (parent : (prepareNormalization q full).indexed.NodeId) :
    (childIDs (prepareNormalization q full).indexed.nodes.size parentWords parent.val).length =
      ((prepareNormalization q full).indexed.children.get parent).size := by
  rw [childIDs_eq_prepared q full parentWords hwords parent, List.length_map, Array.length_toList]

theorem childIDs_length_eq_internalWord (parent : (prepareNormalization q full).indexed.NodeId) :
    (childIDs (prepareNormalization q full).indexed.nodes.size parentWords parent.val).length =
      (givenTreeROM q full).internal.getD ((prepareNormalization q full).indexed.nodes.size + parent.val) 0 := by
  rw [childIDs_length_eq_degree q full parentWords hwords parent]
  exact (UniformNormalizationRAM.givenTreeROM_degree q full parent).symm

theorem flatChildren_eq_givenTreeROM :
    flatChildren (prepareNormalization q full).indexed.nodes.size parentWords = (givenTreeROM q full).children := by
  rw [flatChildren, ← finRange_map_val, List.flatMap_map]
  change (List.finRange (prepareNormalization q full).indexed.nodes.size).flatMap
    (fun parent => childIDs (prepareNormalization q full).indexed.nodes.size parentWords parent.val) =
      (List.finRange (prepareNormalization q full).indexed.nodes.size).flatMap
        (fun parent => ((prepareNormalization q full).indexed.children.get parent).toList.map Fin.val)
  apply congrArg (fun f : (prepareNormalization q full).indexed.NodeId → List Nat =>
    (List.finRange (prepareNormalization q full).indexed.nodes.size).flatMap f)
  funext parent
  exact childIDs_eq_prepared q full parentWords hwords parent

theorem flatChildren_length (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (flatChildren (prepareNormalization q full).indexed.nodes.size parentWords).length =
      (prepareNormalization q full).indexed.nodes.size - 1 := by
  rw [flatChildren_eq_givenTreeROM q full parentWords hwords, givenTreeROM_children_length q full hq hlaminar]

end ParentWords

/-- The protocol is satisfied by the original actual internal parent words. -/
theorem givenTreeROM_parentWords (q : Nat) (full : List (Finset (Fin q)))
    (child : Nat) (hchild : child < (prepareNormalization q full).indexed.nodes.size) :
    (givenTreeROM q full).internal.getD child 0 = encodedNode (prepareNormalization q full).indexed
      ((prepareNormalization q full).indexed.parents.get ⟨child, hchild⟩) :=
  UniformNormalizationRAM.givenTreeROM_parent q full ⟨child, hchild⟩

theorem childIDs_givenTreeROM (q : Nat) (full : List (Finset (Fin q)))
    (parent : (prepareNormalization q full).indexed.NodeId) :
    childIDs (prepareNormalization q full).indexed.nodes.size
        (fun child => (givenTreeROM q full).internal.getD child 0) parent.val =
      ((prepareNormalization q full).indexed.children.get parent).toList.map Fin.val :=
  childIDs_eq_prepared q full _ (givenTreeROM_parentWords q full) parent

theorem flatChildren_givenTreeROM (q : Nat) (full : List (Finset (Fin q))) :
    flatChildren (prepareNormalization q full).indexed.nodes.size
      (fun child => (givenTreeROM q full).internal.getD child 0) = (givenTreeROM q full).children :=
  flatChildren_eq_givenTreeROM q full _ (givenTreeROM_parentWords q full)

end PaperProofs.Structure.LaminarTree.RawCandidateChildrenLayout
