module

public import PaperProofs.Structure.PSTR_RepairHeap_024

/-! Every prefix of the real spill/repair/restore keeps the original
capacity invariant. Scratch is framed through each actual store, not just
at the completed spill, and the repair is used without an intermediate HALT. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRReplyCapacity

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRReplySpill

set_option maxRecDepth 6000 in
theorem spill_prefix_frame {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base : Nat) (hf : state.register .flag = BitVec.ofNat bits base)
    (hroom : Fits bits (base + 3)) (address : Nat) (ha : address < base)
    (count : Nat) (hc : count ≤ 8) :
    (executeOps rom (spillProgram.take count) state).heap (BitVec.ofNat bits address) =
      state.heap (BitVec.ofNat bits address) := by
  have hfit : Fits bits address := ha.trans ((Nat.le_add_right base 3).trans_lt hroom)
  have hne (offset : Nat) (ho : offset ≤ 3) :
      BitVec.ofNat bits address ≠ BitVec.ofNat bits (base + offset) :=
    (ofNat_injective_of_fit _ _ hfit (slot_fit base hroom offset ho)).not.mpr (by omega)
  have hz := hne 0 (by decide)
  simp only [Nat.add_zero] at hz
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  interval_cases count <;>
    simp +decide only [spillProgram, List.take_succ_cons, List.take_zero, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      hf, BitVec.ofNat_add_ofNat, h2, h3, hz, hne 1 (by decide), hne 2 (by decide),
      hne 3 (by decide)]

theorem restore_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) : (executeOps rom (restoreProgram.take count) state).heap = state.heap := by
  by_cases hc : count ≤ 10
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (show restoreProgram.length ≤ count by rw [restore_length]; omega)]
    exact restore_heap rom state

theorem spill_prefix_represents {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords base : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (hf : state.register .flag = BitVec.ofNat bits base) (count : Nat) (hc : count ≤ 8) :
    HeapRepresents q full capWords configuration (executeOps rom (spillProgram.take count) state).heap := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords base state.heap _
    hb hq rep bitmap hr hroom hbase
  intro address ha
  exact spill_prefix_frame rom state base hf hroom address ha count hc

theorem repair_execute_capacity {bits q : Nat} (rom : PhysicalROM)
    (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : Fits bits (4 + packedCapacityWords q capWords bits))
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (count : Nat) (hc : count ≤ 21) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (executeOps rom (PSTRRuntimeRepair.program.take count) state).heap) := by
  have haddr : (state.register .address).toNat < capWords := by
    rw [haddress]
    have ht := tool.isLt
    omega
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstartlt : (state.register .address).toNat * CapacityBits.width q <
      capWords * CapacityBits.width q := Nat.mul_lt_mul_of_pos_right haddr hwp
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) :=
    hstartlt.trans ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  have hptr := PSTRMarkUsedBits.physical_fit_of_offset _ _ hstartlt hr
  have hhead : (PSTRRuntimeMarkUsed.markHeap
      ((state.register .address).toNat * CapacityBits.width q) state.heap
      (BitVec.ofNat bits 2)).toNat = packedCapacityWords q capWords bits := by
    rw [PSTRRuntimeMarkUsed.markHeap_header _ state.heap hb hptr 2 (by decide)]
    exact rep.2.2.1
  have hcap := (rep.2.2.2.2.2.2.2.2 hq).2
  have hz : logicalHeap q capWords state.heap (state.register .address).toNat = 0 := by
    rw [haddress]
    simpa only [unused, decide_false, bit, Bool.false_eq_true, ite_false] using
      rep.2.2.2.2.2.2.2.1 tool
  have hmarked := PSTRMarkUsedHeap.mark_capacity_bounded state.heap capWords
    (state.register .address).toNat (by omega) hq haddr hr hz hcap
  rw [PSTRRepairCapacity.execute_prefix_heap rom state (by omega) hw hwidth rep.2.2.2.1 hstart
    (packedCapacityWords q capWords bits) hhead count hc]
  split_ifs with hfirst hsecond
  · exact hcap
  · exact hmarked
  · intro address ha
    rw [PSTRAdvanceHeap.bump_capacity _ capWords address (by omega) hq ha hr hi]
    exact hmarked address ha

theorem execute_prefix_capacity {bits q : Nat} (rom : PhysicalROM)
    (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords base : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hf : state.register .flag = BitVec.ofNat bits base) (count : Nat) (hc : count ≤ 39) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (executeOps rom (PSTRRepairReply.program.take count) state).heap) := by
  have hmidlen : (spillProgram ++ PSTRRuntimeRepair.program).length = 29 := rfl
  have hsp : HeapRepresents q full capWords configuration (executeOps rom spillProgram state).heap := by
    rw [spill_execute_heap rom state base hf]
    exact PSTRRepairHeap.spill_represents full configuration capWords base state (by omega) hq
      rep bitmap hr hroom hbase
  have hptr : Fits bits (4 + packedCapacityWords q capWords bits) :=
    (show 4 + packedCapacityWords q capWords bits ≤ base + 3 by omega).trans_lt hroom
  have hrepair (steps : Nat) (hs : steps ≤ 21) :
      CapacityPrefixBounded q capWords (logicalHeap q capWords
        (executeOps rom (PSTRRuntimeRepair.program.take steps) (executeOps rom spillProgram state)).heap) :=
    repair_execute_capacity rom full configuration capWords (executeOps rom spillProgram state) tool
      hb hq hw hsp unused bitmap hr hptr (by rw [spill_address]; exact haddress)
      (by rw [spill_width]; exact hwidth) steps hs
  by_cases hs : count ≤ 8
  · rw [PSTRRepairReply.program, List.take_append_of_le_length (by rw [hmidlen]; omega),
      List.take_append_of_le_length (by rw [spill_length]; exact hs)]
    exact ((spill_prefix_represents rom full configuration capWords base state (by omega) hq rep
      bitmap hr hroom hbase hf count hs).2.2.2.2.2.2.2.2 hq).2
  · by_cases hm : count ≤ 29
    · rw [PSTRRepairReply.program, List.take_append_of_le_length (by rw [hmidlen]; exact hm),
        List.take_append, List.take_of_length_le (by rw [spill_length]; omega), executeOps_append]
      exact hrepair _ (by rw [spill_length]; omega)
    · rw [PSTRRepairReply.program, List.take_append, List.take_of_length_le (by rw [hmidlen]; omega),
        executeOps_append, restore_prefix_heap, executeOps_append]
      simpa only [show 21 = PSTRRuntimeRepair.program.length from rfl, List.take_length] using hrepair 21 le_rfl

theorem actual_prefix_capacity {bits q : Nat} (rom : PhysicalROM)
    (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords base : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 40) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (packingRun rom PSTRRepairReply.program count state).heap) := by
  by_cases hbody : count ≤ PSTRRepairReply.program.length
  · rw [packingRun_eq_executeOps_take rom _ _ PSTRRepairReply.program_straight
      (PSTRRepairReply.code_fit hb) (PSTRRepairReply.pc_fit hb) hp ha count hbody]
    exact execute_prefix_capacity rom full configuration capWords base state tool hb hq hw rep unused
      bitmap hr hroom hbase haddress hwidth hf count (by rw [← PSTRRepairReply.program_length]; exact hbody)
  · have he : count = PSTRRepairReply.program.length + 1 := by
      rw [PSTRRepairReply.program_length] at *
      omega
    rw [he, packingRun_executeOps_halt rom _ _ PSTRRepairReply.program_straight
      (PSTRRepairReply.code_fit hb) (PSTRRepairReply.pc_fit hb) hp ha]
    simpa only [show 39 = PSTRRepairReply.program.length from rfl, List.take_length] using
      execute_prefix_capacity rom full configuration capWords base state tool hb hq hw rep unused
        bitmap hr hroom hbase haddress hwidth hf 39 le_rfl

end PaperProofs.Structure.LaminarTree.PSTRReplyCapacity
