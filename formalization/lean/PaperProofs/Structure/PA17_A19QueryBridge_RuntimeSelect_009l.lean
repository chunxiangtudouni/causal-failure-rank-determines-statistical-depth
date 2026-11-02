module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009k

/-! One genuine packed-read/parent-push body. The capacity is obtained from
the original represented packed table by the actual007 reader. It is never
an entry oracle. Physical header/count/parent/candidate cells stay physical;
the table scalar is read through the separate original logicalHeap view. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def readPushProgram : List PackingOp := payloadRead ++ PA17A19RuntimeRead007.cachedProgram ++ pushProgram

theorem readPushProgram_length : readPushProgram.length = 91 := rfl
theorem readPushProgram_straight : StraightProgram readPushProgram := by
  intro op ho
  simp only [readPushProgram, List.mem_append] at ho
  rcases ho with (ho | ho) | ho
  · exact payloadRead_straight op ho
  · exact PA17A19RuntimeRead007.cachedProgram_straight op ho
  · exact pushProgram_straight op ho

theorem execute_readPush {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords header base candidates counts parents node parent count : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hs : Fits bits (4 + capWords * CapacityBits.width q)) (hf : Fits bits heapWords)
    (hheader : header = PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full))
    (hheaderAlloc : header < heapWords)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hp : Fits bits parent) (hc : Fits bits count)
    (hptr : Fits bits (base + node)) (hscalar : base + node < capWords)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base)
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadCount : state.heap (BitVec.ofNat bits (counts + node)) = BitVec.ofNat bits count)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent) :
    let rom := callInput q full command
    let cap := logicalHeap q capWords state.heap (base + node)
    let after := executeOps rom readPushProgram state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .index = BitVec.ofNat bits (candidates + parent) ∧
      after.register .value = pushedValue node parent cap count (state.heap (BitVec.ofNat bits (candidates + parent))) ∧
      after.heap = Function.update state.heap (BitVec.ofNat bits (candidates + parent))
        (pushedValue node parent cap count (state.heap (BitVec.ofNat bits (candidates + parent)))) := by
  let rom := callInput q full command
  let located := executeOps rom payloadRead state
  let loaded := executeOps rom PA17A19RuntimeRead007.cachedProgram located
  have hl := payloadRead_result rom header base node state h1 hn hh hnode hbase
  have hlrep : HeapRepresents q full capWords configuration located.heap := by rw [hl.2.2]; exact rep
  have hr := PA17A19RuntimeRead007.execute_cached full command configuration capWords heapWords located hb hq hw hlrep
    (by rw [hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptr]; exact hscalar) hs hf
    (by simpa only [← hheader] using hheaderAlloc)
    (by rw [hl.2.2]; exact hwidth) (by rw [hl.2.2]; exact hmask)
    (by simpa only [← hheader] using hl.1)
  have hm : loaded.heap = state.heap := hr.2.2.1.trans hl.2.2
  have hvalueNat : (loaded.register .value).toNat = logicalHeap q capWords state.heap (base + node) := by
    rw [hr.2.1, hl.2.2, hl.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hptr]
  have hvalue : loaded.register .value = BitVec.ofNat bits (logicalHeap q capWords state.heap (base + node)) := by
    have he := congrArg (BitVec.ofNat bits) hvalueNat
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  have hcapFit : Fits bits (logicalHeap q capWords state.heap (base + node)) := by
    rw [← hvalueNat]
    exact BitVec.isLt _
  have hpush := pushProgram_result rom header candidates counts parents node parent
    (logicalHeap q capWords state.heap (base + node)) count loaded h1 hn hp hcapFit hc
    (by simpa only [← hheader] using hr.1) hvalue
    (by rw [hm]; exact hnode) (by rw [hm]; exact hcandidates) (by rw [hm]; exact hcounts)
    (by rw [hm]; exact hparents) (by rw [hm]; exact hreadCount) (by rw [hm]; exact hreadParent)
  rw [hm] at hpush
  dsimp only
  simpa only [readPushProgram, executeOps_append] using hpush

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
