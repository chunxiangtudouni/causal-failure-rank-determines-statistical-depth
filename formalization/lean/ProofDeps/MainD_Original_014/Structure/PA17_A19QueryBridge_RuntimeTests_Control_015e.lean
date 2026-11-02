module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015d

/-! Every actual ancestor-body prefix preserves every Word cell outside the
three real scratch stores. Reader scratch registers may change; its complete
heap-prefix frame is used, and H is recovered by the actual cached reader. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem ancestorKernel_prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
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
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (ha : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) =
      BitVec.ofNat bits encoded)
    (hr : remaining < treeSize q full) (hn : encoded ≤ treeSize q full)
    (hscalar : entryBase + 1 + (encoded - 1) < capWords)
    (address : BitVec bits)
    (h11 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11))
    (h12 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12))
    (h14 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 14))
    (count : Nat) (hcut : count ≤ 109) :
    (executeOps (callInput q full command) (ancestorKernel.take count) state).heap address = state.heap address := by
  let rom := callInput q full command
  let workspace := PSTRQueryLayout.physicalWorkspace full capWords bits
  let header := PSTRQueryLayout.header workspace (treeSize q full)
  let lead := executeOps rom ancestorLead state
  let read := executeOps rom PA17A19RuntimeRead007.cachedProgram lead
  let counted := executeOps rom ancestorCountRead read
  let compared := executeOps rom extensionCompare counted
  have hroom : Fits bits (header + 16) := halloc.trans hf
  have hheader : Fits bits header := (Nat.le_add_right header 16).trans_lt hroom
  have hremain : Fits bits (remaining + 1) := (show remaining + 1 ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hencoded : Fits bits encoded := (show encoded ≤ header by
    unfold header PSTRQueryLayout.header; omega).trans_lt hheader
  have hl := execute_ancestorLead rom header remaining entryBase encoded state hroom hremain hencoded hh hc he ha
  have hframe : ∀ physical < header + 8, lead.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    intro physical hp
    rw [hl.1]
    exact update_leading_frame state.heap header 12 _ hroom (by decide) (by decide) physical hp
  have hread := cached_of_leading_frame full command configuration capWords heapWords
    (entryBase + 1 + (encoded - 1)) state lead hb hq hw rep bitmap hs hf halloc hframe hwidth hmask
    hl.2.2 hl.2.1 hscalar
  have hsize : (read.heap (BitVec.ofNat bits 0)).toNat = treeSize q full := by
    rw [hread.2.2, hframe 0 (by omega)]
    exact rep.1
  have hne : BitVec.ofNat bits (header + 11) ≠ BitVec.ofNat bits (header + 12) := by
    intro heq
    have hi := (slots_eq_iff header 11 12 hroom (by decide) (by decide)).mp heq
    omega
  have hnode : read.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits encoded := by
    rw [hread.2.2, hl.1, Function.update_of_ne hne]
    exact ha
  have hcount := execute_ancestorCountRead rom workspace (treeSize q full) encoded read
    (by omega) hencoded hheader hsize hread.1 hnode
  have hcompare := execute_extensionCompare rom header counted hcount.2.2.1
  have hcountNo : ∀ op ∈ ancestorCountRead, HeapPreservingOp op := by
    simp [ancestorCountRead, countsLocator, ancestorReadSuffix, loadSlot, HeapPreservingOp]
  change (executeOps rom ((ancestorLead ++ PA17A19RuntimeRead007.cachedProgram ++ ancestorTail).take count)
    state).heap address = state.heap address
  apply executeOps_prefix_frame_append rom (ancestorLead ++ PA17A19RuntimeRead007.cachedProgram) ancestorTail state address
  · intro cut hcut'
    apply executeOps_prefix_frame_append rom ancestorLead PA17A19RuntimeRead007.cachedProgram state address
    · intro index hi
      exact ancestorLead_prefix_frame rom header state hh address h12 index (by simpa only [ancestorLead_length] using hi)
    · intro index _
      rw [executeOps_prefix_noStore rom PA17A19RuntimeRead007.cachedProgram lead
        PA17A19RuntimeRead007.cachedProgram_noStore index]
    · exact hcut'
  · intro cut hcut'
    change (executeOps rom ((ancestorCountRead ++ extensionCompare ++ parentTail).take cut) read).heap address = read.heap address
    apply executeOps_prefix_frame_append rom (ancestorCountRead ++ extensionCompare) parentTail read address
    · intro index hi
      apply executeOps_prefix_frame_append rom ancestorCountRead extensionCompare read address
      · intro clock _
        rw [executeOps_prefix_noStore rom ancestorCountRead read hcountNo clock]
      · intro clock hclock
        exact extensionCompare_prefix_frame rom header counted hcount.2.2.1 address h14 clock
          (by simpa only [extensionCompare_length] using hclock)
      · exact hi
    · intro index hi
      change (executeOps rom (parentTail.take index) compared).heap address = compared.heap address
      exact parentTail_prefix_frame rom header compared hcompare.2.2 address h11 index
        (by simpa only [parentTail_length] using hi)
    · exact hcut'
  · change count ≤ ancestorKernel.length
    rw [ancestorKernel_length]
    exact hcut

theorem actual_ancestorBody_prefix_frame {bits q origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords entryBase remaining encoded : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
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
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 227))) (hactive : state.halted = false)
    (hc : state.register .total = BitVec.ofNat bits (remaining + 1))
    (he : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 13)) =
      BitVec.ofNat bits entryBase)
    (ha : state.heap (BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11)) =
      BitVec.ofNat bits encoded)
    (hr : remaining < treeSize q full) (hn : encoded ≤ treeSize q full)
    (hscalar : entryBase + 1 + (encoded - 1) < capWords)
    (address : BitVec bits)
    (h11 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 11))
    (h12 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 12))
    (h14 : address ≠ BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) + 14))
    (count : Nat) (hcut : count ≤ 112) :
    (packingRun (callInput q full command) containing count state).heap address = state.heap address := by
  rw [actual_ancestor_prefix em (callInput q full command) state hp hactive count hcut, ancestorBody_as_kernel]
  apply executeOps_prefix_frame_append (callInput q full command) ancestorKernel (back (5 * (origin + 222))) state address
  · intro cut hcut'
    exact ancestorKernel_prefix_frame full command configuration capWords heapWords entryBase remaining encoded state
      hb hq hw rep bitmap hs hf halloc hwidth hmask hh hc he ha hr hn hscalar address h11 h12 h14 cut
      (by simpa only [ancestorKernel_length] using hcut')
  · intro cut _
    apply congrFun (executeOps_prefix_noStore _ _ _ ?_ cut) address
    simp [back, backLead, HeapPreservingOp]
  · simpa only [← ancestorBody_as_kernel, ancestorBody_length] using hcut

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
