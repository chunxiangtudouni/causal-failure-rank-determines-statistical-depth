module

public import PaperProofs.Structure.PSTR_CountReady_061
public import PaperProofs.Structure.PSTR_LeafCertifiedPrefix_070

/-! The outer invariant genuinely supplies the node kernel's incoming
registers by executing its header test, leaf read and real slot reloads.
EVERY actual prefix keeps the SAME heap at the SAME returned duration.
The executable input remains ORIGINAL callInput; no leaf/count/offset answer
is supplied as a new original caller qualification. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafCountPrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace


theorem test_prefix_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start exit : Nat)
    (hbound : start + (PSTRCountControl.testBlock exit).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (PSTRCountControl.testBlock exit).length),
      whole[start + i]'(by omega) = (PSTRCountControl.testBlock exit)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 5) :
    packingRun rom whole count state = executeOps rom ((PSTRCountControl.testBlock exit).take count) state := by
  apply PSTRWordSegments.segment_prefix rom whole (PSTRCountControl.testLead exit)
    (.jumpIfZero .flag .address) start
    (by rw [PSTRCountControl.testBlock_length, PSTRCountControl.testLead_length] at *; omega)
    ?_ ?_ (PSTRCountControl.testLead_straight exit) hw hpcfit state hp ha count hc
  · intro i hi
    exact (hcode i (by rw [PSTRCountControl.testBlock_length]; rw [PSTRCountControl.testLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (hcode (PSTRCountControl.testLead exit).length
      (by rw [PSTRCountControl.testBlock_length, PSTRCountControl.testLead_length]; decide)).trans
      (List.getElem_append_right' (PSTRCountControl.testLead exit)
        (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

theorem test_prefix_heap {bits : Nat} (rom : PhysicalROM) (exit : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 5) :
    (executeOps rom ((PSTRCountControl.testBlock exit).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem restore_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (PSTRCountRestore.program.take count) state).heap = state.heap := by
  apply AlgorithmClaims.PackedCapacityRAM.executeOps_heap_of_no_store
  intro op ho
  have hno : ∀ entry ∈ PSTRCountRestore.program, AlgorithmClaims.PackedCapacityRAM.HeapPreservingOp entry := by
    simp [PSTRCountRestore.program, PSTRCountWorkspace.program, PSTRCountRestore.restore,
      AlgorithmClaims.PackedCapacityRAM.HeapPreservingOp]
  exact hno op (List.mem_of_mem_take ho)

theorem actual_entry {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (state : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q)
    (ready : PSTRCountReady.Ready full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node.val state) :
    ∃ steps ≤ 118,
      let bits := indexWidth 32 full.length q
      let capWords := capacityWords 8192 full.length q (treeSize q full)
      let workspace := base q full capWords bits
      let after := packingRun (callInput q full command) whole steps state
      (after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 123)) ∧
        after.heap = state.heap ∧ after.register .old = BitVec.ofNat bits (countsBase workspace) ∧
        after.register .index = BitVec.ofNat bits node.val ∧
        after.register .fresh = BitVec.ofNat bits (PSTRCountChildRows.flatOffset full node.val) ∧
        after.register .value = BitVec.ofNat bits
          ((IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node)) ∧
      (∀ clock ≤ steps, (packingRun (callInput q full command) whole clock state).heap = state.heap) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let rom := callInput q full command
  let tested := executeOps rom (PSTRCountControl.testBlock (origin + 478)) state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have dimensions := PSTROriginalCountRoom.dimension_rooms full
  have hsize : Fits bits (prepareNormalization q full).indexed.nodes.size :=
    (Nat.le_succ _).trans_lt dimensions.2.2.1
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using
      (PSTRStaticHeap.headers full configuration capWords state.heap ready.rep).1
  have test_pc : tested.pc = BitVec.ofNat bits (5 * (origin + 10)) := by
    simpa only [Nat.add_assoc] using PSTRCountControl.test_pc_of_lt rom (origin + 5) (origin + 478)
      (prepareNormalization q full).indexed.nodes.size node.val state ready.pc ht ready.index hsize node.isLt
  have test_active : tested.halted = false := by rw [executeOps_halted, ready.active]
  have test_heap : tested.heap = state.heap := (PSTRCountControl.test_payload rom (origin + 478) state).1
  have test_rep : HeapRepresents q full capWords configuration tested.heap := by rw [test_heap]; exact ready.rep
  have test_index : tested.register .index = BitVec.ofNat bits node.val :=
    (PSTRCountControl.test_payload rom (origin + 478) state).2.1.trans ready.index
  have savedWidth : tested.heap (BitVec.ofNat bits (workspace + 12)) = BitVec.ofNat bits (CapacityBits.width q) := by
    rw [test_heap]
    simpa only [Nat.add_zero, ↓reduceIte] using ready.slots 0 (by decide)
  have savedMask : tested.heap (BitVec.ofNat bits (workspace + 13)) = lowMask bits (CapacityBits.width q) := by
    rw [test_heap]
    simpa +decide only [Nat.add_assoc, ↓reduceIte] using ready.slots 1 (by decide)
  have ht1 : Fits bits (treeSize q full + 1) := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using dimensions.2.2.1
  obtain ⟨leafSteps, hleafSteps, leafResult⟩ := PSTRLeafCertifiedPrefix.actual_leaf whole (origin + 10)
    (PSTROuterCountCode.leaf_at whole origin hc) hwords hpcfit full command configuration capWords tested node
    (by omega) hq (PA17PackingBounds043.width_le_bits full.length q) test_rep
    (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
    dimensions.1 dimensions.2.1 ht1 dimensions.2.2.2.1 test_index savedWidth savedMask test_pc test_active
  let leafed := packingRun rom whole leafSteps tested
  have leaf_rep : HeapRepresents q full capWords configuration leafed.heap := by
    rw [leafResult.2.2.1]
    exact test_rep
  have leaf_pc : leafed.pc = BitVec.ofNat bits (5 * (origin + 97)) := by
    simpa only [Nat.add_assoc] using leafResult.2.1
  have leaf_word : leafed.register .value = BitVec.ofNat bits
      ((IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node) := by
    have he := congrArg (BitVec.ofNat bits) leafResult.2.2.2.1
    simpa only [bits, BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  let restored := executeOps rom PSTRCountRestore.program leafed
  have data := PSTRCountRestore.execute_entry full command configuration capWords leafed (by omega) hq leaf_rep
  have restore_pc : restored.pc = BitVec.ofNat bits (5 * (origin + 123)) := by
    rw [executeOps_pc rom PSTRCountRestore.program leafed PSTRCountRestore.program_straight,
      leaf_pc, PSTRCountRestore.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have restore_active : restored.halted = false := by rw [executeOps_halted, leafResult.1]
  have restore_heap : restored.heap = state.heap := data.2.2.2.2.trans (leafResult.2.2.1.trans test_heap)
  have restore_index : restored.register .index = BitVec.ofNat bits node.val := by
    rw [data.2.1, leafResult.2.2.1, test_heap]
    simpa +decide only [Nat.add_assoc, ↓reduceIte] using ready.slots 2 (by decide)
  have restore_offset : restored.register .fresh = BitVec.ofNat bits (PSTRCountChildRows.flatOffset full node.val) := by
    rw [data.2.2.1, leafResult.2.2.1, test_heap]
    simpa +decide only [Nat.add_assoc, ↓reduceIte] using ready.slots 3 (by decide)
  have ts := PSTROuterCountCode.test_at whole origin hc
  have rs := PSTROuterCountCode.restore_at whole origin hc
  have test_run := PSTRCountControl.fetched_test rom whole (origin + 5) (origin + 478) ts.bound ts.code hwords hpcfit
    state ready.pc ready.active
  have restore_run := PSTRCountRestore.containing_run rom whole (origin + 97) rs.bound rs.code hwords hpcfit
    leafed leaf_pc leafResult.1
  refine ⟨5 + (leafSteps + 26), by omega, ?_, ?_⟩
  · rw [PSTRWordSegments.run_add, test_run, PSTRWordSegments.run_add, restore_run]
    exact ⟨restore_active, restore_pc, restore_heap, data.2.2.2.1, restore_index, restore_offset, data.1.trans leaf_word⟩
  · intro clock hclock
    by_cases htest : clock ≤ 5
    · rw [test_prefix_run rom whole (origin + 5) (origin + 478) ts.bound ts.code hwords hpcfit
        state ready.pc ready.active clock htest]
      exact test_prefix_heap rom (origin + 478) state clock htest
    · by_cases hleaf : clock - 5 ≤ leafSteps
      · rw [show clock = 5 + (clock - 5) by omega, PSTRWordSegments.run_add, test_run]
        exact (leafResult.2.2.2.2 (clock - 5) hleaf).trans test_heap
      · rw [show clock = 5 + (leafSteps + (clock - (5 + leafSteps))) by omega,
          PSTRWordSegments.run_add, test_run, PSTRWordSegments.run_add,
          PSTRWidthPrefix.straight_prefix rom whole PSTRCountRestore.program (origin + 97)
            rs.bound rs.code PSTRCountRestore.program_straight hwords hpcfit leafed leaf_pc leafResult.1
            (clock - (5 + leafSteps)) (by rw [PSTRCountRestore.program_length]; omega),
          restore_prefix_heap, leafResult.2.2.1, test_heap]

end PaperProofs.Structure.LaminarTree.PSTRLeafCountPrefix
