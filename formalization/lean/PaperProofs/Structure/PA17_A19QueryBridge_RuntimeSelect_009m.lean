module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009l

/-! A complete actual105-instruction reverse-parent iteration. The only
capacity used is the original packed table scalar read by007 in this run.
The runtime node word is decremented in heap and the machine remains ACTIVE
at the actual backedge. No Nat/physical mixed-heap convention is used. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_reverse_push {bits q origin : Nat} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing) (full : List (Finset (Fin q))) (command : Command)
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
    (h1 : Fits bits 1) (hn : Fits bits (node + 1)) (hparent : Fits bits parent) (hc : Fits bits count)
    (hptr : Fits bits (base + node)) (hscalar : base + node < capWords)
    (hbelow : header + 12 < candidates) (htarget : Fits bits (candidates + parent + 1))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hnode : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1))
    (hbase : state.heap (BitVec.ofNat bits (header + 9)) = BitVec.ofNat bits base)
    (hcandidates : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits candidates)
    (hcounts : state.heap (BitVec.ofNat bits (header + 11)) = BitVec.ofNat bits counts)
    (hparents : state.heap (BitVec.ofNat bits (header + 12)) = BitVec.ofNat bits parents)
    (hreadCount : state.heap (BitVec.ofNat bits (counts + node)) = BitVec.ofNat bits count)
    (hreadParent : state.heap (BitVec.ofNat bits (parents + (node + 1))) = BitVec.ofNat bits parent) :
    let cap := logicalHeap q capWords state.heap (base + node)
    let selected := pushedValue node parent cap count (state.heap (BitVec.ofNat bits (candidates + parent)))
    let after := packingRun (callInput q full command) containing 105 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * origin) ∧
      after.register .address = BitVec.ofNat bits header ∧ after.register .total = BitVec.ofNat bits node ∧
      after.register .flag = BitVec.ofNat bits 0 ∧
      after.heap = Function.update
        (Function.update state.heap (BitVec.ofNat bits (candidates + parent)) selected)
        (BitVec.ofNat bits (header + 8)) (BitVec.ofNat bits node) := by
  let rom := callInput q full command
  let tested := executeOps rom (reverseTest origin) state
  let pushed := executeOps rom readPushProgram tested
  have ht := reverseTest_result rom origin header (node + 1) state hn hh hp hnode
  have htestRep : HeapRepresents q full capWords configuration tested.heap := by rw [ht.2.2]; exact rep
  have hr := execute_readPush full command configuration capWords heapWords header base candidates counts parents node parent count
    tested hb hq hw htestRep hs hf hheader hheaderAlloc
    (by rw [ht.2.2]; exact hwidth) (by rw [ht.2.2]; exact hmask)
    h1 hn hparent hc hptr hscalar ht.2.1
    (by rw [ht.2.2]; exact hnode) (by rw [ht.2.2]; exact hbase)
    (by rw [ht.2.2]; exact hcandidates) (by rw [ht.2.2]; exact hcounts)
    (by rw [ht.2.2]; exact hparents) (by rw [ht.2.2]; exact hreadCount) (by rw [ht.2.2]; exact hreadParent)
  rw [ht.2.2] at hr
  have hne : BitVec.ofNat bits (header + 8) ≠ BitVec.ofNat bits (candidates + parent) := by
    apply (ofNat_injective_of_fit _ _
      ((show header + 8 ≤ candidates + parent + 1 by omega).trans_lt htarget)
      ((Nat.le_succ _).trans_lt htarget)).not.mpr
    omega
  have hremaining : pushed.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits (node + 1) := by
    rw [hr.2.2.2, Function.update_of_ne hne]
    exact hnode
  have hfoot := reverseFoot_result rom origin header node pushed h1 hn hr.1 hremaining
  have he : reverseBody origin = readPushProgram ++ reverseFoot origin := by
    simp only [reverseBody, reverseBodyLead, readPushProgram, reverseFoot, List.append_assoc]
  have hrun : packingRun rom containing 105 state = executeOps rom (reverseFoot origin) pushed := by
    rw [(fetched_reverse_iteration em rom header node state hn hh hp ha hnode).1, he, executeOps_append]
  dsimp only
  rw [hrun]
  refine ⟨?_, hfoot.2.2.2.1, hfoot.1, hfoot.2.1, hfoot.2.2.1, ?_⟩
  · rw [executeOps_halted, executeOps_halted, executeOps_halted, ha]
  · rw [hfoot.2.2.2.2, hr.2.2.2]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
