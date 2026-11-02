module

public import PaperProofs.Structure.PSTR_HD_CountBody_032

/-! Relate the physical-array loop specification to the ORIGINAL countNode
and usedCounts theorems. countROM below is used ONLY in a mathematical
specification equality, never as the actual kernel's runtime ROM. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountSpec

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open IndexedUsedCounts IndexedDescent PSTRCountBounds

def nodeResult {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (countsBase offset : Nat) : Nat :=
  if bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) = 0 then
    (leafBitmap (prepareNormalization q full).indexed used).get node
  else prefixSum full heap countsBase offset ((prepareNormalization q full).indexed.children.get node).size

theorem original_countNode_value {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (countsBase offset : Nat) :
    let cache := (prepareNormalization q full).indexed
    let initial : IndexedRAM.State := ⟨fun _ => 0,
      fun child => (heap (BitVec.ofNat bits (countsBase + child))).toNat, 0⟩
    (IndexedRAM.execute (countROM cache used)
      (countNode node.val offset (cache.children.get node).size) initial).heap node.val =
        nodeResult full used node heap countsBase offset := by
  dsimp only
  rw [execute_countNode_heap, Function.update_self]
  simp only [countROM, ROM.withInput, treeROM, node.isLt, ↓reduceDIte]
  change (if bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) = 0 then
      vectorMemory (leafBitmap (prepareNormalization q full).indexed used) node.val
    else prefixSum full heap countsBase offset ((prepareNormalization q full).indexed.children.get node).size) = _
  rw [vectorMemory_at]
  rfl

theorem actual_child_sum {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (countsBase offset : Nat)
    (hq : 0 < q) (hl : LaminarSchedule full) (hqfit : Fits bits q)
    (row : ∀ position (hp : position < ((prepareNormalization q full).indexed.children.get node).size),
      (PSTRStaticLayout.childWords q full).getD (offset + position) 0 =
        (((prepareNormalization q full).indexed.children.get node)[position]).val)
    (previous : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node.val →
      heap (BitVec.ofNat bits (countsBase + child.val)) =
        BitVec.ofNat bits ((usedCounts (prepareNormalization q full).indexed used).get child)) :
    prefixSum full heap countsBase offset ((prepareNormalization q full).indexed.children.get node).size =
      (prepareNormalization q full).indexed.childSum (usedCounts (prepareNormalization q full).indexed used) node := by
  apply congrArg List.sum
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, Array.length_toList]
  · intro position hleft _
    have hp : position < ((prepareNormalization q full).indexed.children.get node).size := by
      simpa only [List.length_map, List.length_range] using hleft
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [row position hp]
    let child := ((prepareNormalization q full).indexed.children.get node)[position]
    have hbefore : child.val < node.val :=
      prepared_child_index_lt q full hq hl node child (Array.getElem_mem_toList hp)
    rw [previous child hbefore, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ((usedCount_bound (prepareNormalization q full).indexed used child).trans_lt hqfit)]

theorem nodeResult_eq_usedCount {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId)
    (heap : BitVec bits → BitVec bits) (countsBase offset : Nat)
    (hq : 0 < q) (hl : LaminarSchedule full) (hqfit : Fits bits q)
    (row : ∀ position (hp : position < ((prepareNormalization q full).indexed.children.get node).size),
      (PSTRStaticLayout.childWords q full).getD (offset + position) 0 =
        (((prepareNormalization q full).indexed.children.get node)[position]).val)
    (previous : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node.val →
      heap (BitVec.ofNat bits (countsBase + child.val)) =
        BitVec.ofNat bits ((usedCounts (prepareNormalization q full).indexed used).get child)) :
    nodeResult full used node heap countsBase offset =
      (usedCounts (prepareNormalization q full).indexed used).get node := by
  by_cases hi : 1 < ((prepareNormalization q full).indexed.decode node).card
  · have hb := (metadata_isInternal (prepareNormalization q full).indexed node).mpr hi
    calc
      _ = prefixSum full heap countsBase offset ((prepareNormalization q full).indexed.children.get node).size := by
        simp [nodeResult, hb, bit]
      _ = _ := (actual_child_sum full used node heap countsBase offset hq hl hqfit row previous).trans
        (prepared_count_childSum q full hq hl used node hi)
  · have hb : (prepareNormalization q full).indexed.metadata.isInternal.get node = false := by
      cases he : (prepareNormalization q full).indexed.metadata.isInternal.get node with
      | false => rfl
      | true => exact False.elim (hi ((metadata_isInternal (prepareNormalization q full).indexed node).mp he))
    calc
      _ = (leafBitmap (prepareNormalization q full).indexed used).get node := by simp [nodeResult, hb, bit]
      _ = _ := prepared_leafBitmap_leaf q full hq used node hi

end PaperProofs.Structure.LaminarTree.PSTRCountSpec
