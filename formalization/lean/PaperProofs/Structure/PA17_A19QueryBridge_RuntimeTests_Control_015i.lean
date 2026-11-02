module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015g
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010p

/-! Every actual node-body prefix preserves all Word cells outside H9/H10. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem nodeLead_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 9))
    (count : Nat) (hc : count ≤ 11) :
    (executeOps rom (nodeLead.take count) state).heap address = state.heap address := by
  let before := nodeLead.take 2
  let after := nodeLead.drop 5
  have heq : nodeLead = before ++ storeSlot 9 .total ++ after := rfl
  rw [heq]
  apply singleSlot_prefix_frame rom before after header 9 .total state
  · simp [before, nodeLead, HeapPreservingOp]
  · simp [after, nodeLead, loadSlot, storeSlot, HeapPreservingOp]
  · simp +decide [before, nodeLead, executeOps, packingExecuteOp, wordOp, wordInstruction, hh]
  · exact hne
  · rw [← heq, nodeLead_length]; exact hc

theorem acceptCompare_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat)
    (state : WordState bits) (hh : state.register .address = BitVec.ofNat bits header)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 10))
    (count : Nat) (hc : count ≤ 9) :
    (executeOps rom (acceptCompare.take count) state).heap address = state.heap address := by
  let before := acceptCompare.take 6
  have heq : acceptCompare = before ++ storeSlot 10 .flag ++ [] := rfl
  rw [heq]
  apply singleSlot_prefix_frame rom before [] header 10 .flag state
  · simp [before, acceptCompare, loadSlot, HeapPreservingOp]
  · simp
  · simp +decide [before, acceptCompare, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction, hh]
  · exact hne
  · rw [← heq, acceptCompare_length]; exact hc

theorem nodeKernel_prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase node : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (halloc : PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16 < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (hc : state.register .total = BitVec.ofNat bits (node + 1))
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (hn : node < treeSize q full) (hscalar : entryBase + 1 + node < capWords)
    (address : BitVec bits)
    (h9 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 9))
    (h10 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 10))
    (count : Nat) (hcut : count ≤ 90) :
    (executeOps (callInput q full command) (nodeKernel.take count) state).heap address = state.heap address := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom nodeLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  let counted := executeOps rom nodeCountRead read
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hnodefit : Fits bits (node + 1) := (show node + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hl := execute_nodeLead rom header node entryBase state hroom hnodefit hh hc he
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    exact update_leading_frame state.heap header 9 _ hroom (by decide) (by decide) physical hp
  have hread := cached_of_leading_frame full command configuration capWords heapWords
    (entryBase + 1 + node) state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hmask
    hl.2.2 hl.2.1 hscalar
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [hread.2.2, hframe 0 (by omega)]
    exact rep.1
  have hnode : read.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits node := by
    rw [hread.2.2, hl.1, Function.update_self]
  have hcount := execute_nodeCountRead rom workspace (treeSize q full) node read (by omega) hheader hsize hread.1 hnode
  have hcountNo : ∀ op ∈ nodeCountRead, HeapPreservingOp op := by
    simp [nodeCountRead, countsLocator, nodeReadSuffix, loadSlot, HeapPreservingOp]
  change (executeOps rom ((nodeLead ++ PA17A19RuntimeRead007.cachedProgram ++ nodeTail).take count) state).heap address = state.heap address
  apply executeOps_prefix_frame_append rom (nodeLead ++ PA17A19RuntimeRead007.cachedProgram) nodeTail state address
  · intro cut hcut'
    apply executeOps_prefix_frame_append rom nodeLead PA17A19RuntimeRead007.cachedProgram state address
    · intro index hi
      exact nodeLead_prefix_frame rom header state hh address h9 index (by simpa only [nodeLead_length] using hi)
    · intro index _
      rw [executeOps_prefix_noStore rom PA17A19RuntimeRead007.cachedProgram lead
        PA17A19RuntimeRead007.cachedProgram_noStore index]
    · exact hcut'
  · intro cut hcut'
    change (executeOps rom ((nodeCountRead ++ acceptCompare).take cut) read).heap address = read.heap address
    apply executeOps_prefix_frame_append rom nodeCountRead acceptCompare read address
    · intro index _
      rw [executeOps_prefix_noStore rom nodeCountRead read hcountNo index]
    · intro index hi
      exact acceptCompare_prefix_frame rom header counted hcount.2.2.1 address h10 index
        (by simpa only [acceptCompare_length] using hi)
    · exact hcut'
  · change count ≤ nodeKernel.length
    rw [nodeKernel_length]
    exact hcut

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
