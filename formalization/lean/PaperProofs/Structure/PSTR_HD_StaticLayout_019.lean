module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.RawTreeSerialization
import Mathlib.Tactic.IntervalCases

/-! Exact offsets in the ORIGINAL cached staticMetadata. These are derived
layout formulas, not additional ROM fields or a different metadata format. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRStaticLayout

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

def childWords (q : Nat) (full : List (Finset (Fin q))) : List Nat :=
  let cache := (prepareNormalization q full).indexed
  (List.finRange cache.nodes.size).flatMap (fun node => (cache.children.get node).toList.map Fin.val)

def edgeCount (q : Nat) (full : List (Finset (Fin q))) : Nat := (childWords q full).length

def chunks (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) : List (List Nat) :=
  let cache := (prepareNormalization q full).indexed
  let nodes := List.finRange cache.nodes.size
  let metadata := IndexedStaticMetadata.buildPositive q full hq
  [[edgeCount q full],
   nodes.map (fun node => encodedNode cache (cache.parents.get node)),
   nodes.map (fun node => (cache.children.get node).size),
   childWords q full,
   nodes.map (fun node => cache.metadata.cardinalities.get node),
   nodes.map (fun node => bit (cache.metadata.isInternal.get node)),
   nodes.map (fun node => match (IndexedDescent.leafTools cache).get node with
     | none => 0 | some tool => tool.val + 1),
   (List.finRange full.length).map (fun stage => encodedNode cache (metadata.stageNodes.get stage)),
   (List.finRange q).map (fun tool => (metadata.toolNodes.get tool).val + 1)]

/-- Segment0 is the flat-child length;1 parents;2 degrees;3 flat children;
4 cards;5 internal flags;6 leaf labels;7 stage nodes;8 tool nodes. -/
def offset (q : Nat) (full : List (Finset (Fin q))) : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1 + (prepareNormalization q full).indexed.nodes.size
  | 3 => 1 + 2 * (prepareNormalization q full).indexed.nodes.size
  | 4 => 1 + 2 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full
  | 5 => 1 + 3 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full
  | 6 => 1 + 4 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full
  | 7 => 1 + 5 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full
  | _ => 1 + 5 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full + full.length

theorem metadata_chunks (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    staticMetadata q full = (chunks q full hq).flatten := by
  unfold staticMetadata
  rw [dite_eq_left hq]
  simp only [chunks, edgeCount, childWords, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
  rfl

theorem metadata_length (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    (staticMetadata q full).length =
      1 + 5 * (prepareNormalization q full).indexed.nodes.size + edgeCount q full + full.length + q := by
  rw [metadata_chunks q full hq]
  simp [chunks, edgeCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.succ_mul]

theorem offset_eq_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (segment : Nat) (hs : segment < 9) :
    ((chunks q full hq).take segment).flatten.length = offset q full segment := by
  interval_cases segment <;>
    simp [chunks, offset, edgeCount, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.succ_mul]

theorem flatten_getD (lists : List (List Nat)) (segment position : Nat)
    (hs : segment < lists.length) (hp : position < lists[segment].length) :
    lists.flatten.getD ((lists.take segment).flatten.length + position) 0 = lists[segment][position] := by
  induction lists generalizing segment with
  | nil => simp at hs
  | cons first later ih =>
    cases segment with
    | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.zero_add,
        List.flatten_cons, List.getElem_cons_zero] at hp ⊢
      rw [List.getD_append _ _ _ _ hp, List.getD_eq_getElem _ _ hp]
    | succ segment =>
      have hs' : segment < later.length := by simpa using hs
      have hp' : position < later[segment].length := by simpa using hp
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append,
        List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have he : first.length + (later.take segment).flatten.length + position - first.length =
          (later.take segment).flatten.length + position := by omega
      rw [he]
      exact ih segment hs' hp'

theorem metadata_chunk_getD (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (segment position : Nat) (hs : segment < 9)
    (hp : position < (chunks q full hq)[segment].length) :
    (staticMetadata q full).getD (offset q full segment + position) 0 =
      (chunks q full hq)[segment][position] := by
  rw [metadata_chunks q full hq, ← offset_eq_prefix q full hq segment hs]
  exact flatten_getD _ segment position (by simpa [chunks] using hs) hp

theorem chunk_in_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (segment position : Nat) (hs : segment < 9)
    (hp : position < (chunks q full hq)[segment].length) :
    offset q full segment + position < (staticMetadata q full).length := by
  rw [metadata_length q full hq]
  interval_cases segment <;> simp [chunks, offset, edgeCount] at hp ⊢ <;> omega

theorem mapped_finRange_get {n : Nat} (f : Fin n → Nat) (index : Fin n) :
    ((List.finRange n).map f)[index.val]'(by simp) = f index := by
  simp only [List.getElem_map, List.getElem_finRange]
  exact congrArg f (Fin.ext rfl)

theorem edgeCount_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) : edgeCount q full = (prepareNormalization q full).indexed.nodes.size - 1 := by
  exact RawTreeSerialization.givenTreeROM_children_length q full hq hl

theorem metadata_index_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (indexFactor : Nat) (hi : 8 ≤ indexFactor) :
    2 + (staticMetadata q full).length ≤
      indexFactor * (full.length + q + treeSize q full + 1) := by
  rw [metadata_length q full hq, edgeCount_eq q full hq hl]
  have hm := Nat.mul_le_mul_right (full.length + q + treeSize q full + 1) hi
  simp only [treeSize, ne_of_gt hq, ite_false] at hm ⊢
  omega

end PaperProofs.Structure.LaminarTree.PSTRStaticLayout
