module

public import Structure.PSTR_RepairReply_023
public import Structure.PSTR_RepairCapacity_018

/-! Scratch writes beyond the original metadata preserve the original heap
representation. Apply this to the actual spill and then the actual contiguous
repair; the final restore changes no heap cell. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRepairHeap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRReplySpill

theorem logical_frame {bits q : Nat} (old fresh : BitVec bits → BitVec bits)
    (capWords indexWords base address : Nat) (hb : 0 < bits) (hq : 0 < q)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + indexWords ≤ base)
    (hframe : ∀ physical < base, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (ha : address < capWords + indexWords) :
    logicalHeap q capWords fresh address = logicalHeap q capWords old address := by
  by_cases hc : address < capWords
  · rw [PSTRMarkUsedBits.scalar_stream _ _ _ hq hc hr,
      PSTRMarkUsedBits.scalar_stream _ _ _ hq hc hr]
    apply congrArg CapacityBits.decodeScalar
    apply congrArg List.ofFn
    funext i
    have hm := Nat.mul_le_mul_right (CapacityBits.width q) (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at hm
    have hoff : address * CapacityBits.width q + i.val < capWords * CapacityBits.width q := by
      have hi := i.isLt
      omega
    have hd : (address * CapacityBits.width q + i.val) / bits <
        packedCapacityWords q capWords bits :=
      (Nat.div_lt_iff_lt_mul hb).mpr
        (hoff.trans_le (packedCapacityWords_mul_bits q capWords hb))
    unfold PSTRMarkUsedBits.bitAt
    rw [hframe _ (by omega)]
  · have hphysical : 4 + packedCapacityWords q capWords bits + (address - capWords) < base := by omega
    have hid : Fits bits (packedCapacityWords q capWords bits + (address - capWords)) := by
      exact (show packedCapacityWords q capWords bits + (address - capWords) ≤
        4 + packedCapacityWords q capWords bits + (address - capWords) by omega).trans_lt
        (hphysical.trans ((Nat.le_add_right base 3).trans_lt hroom))
    simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, hc]
    rw [PSTRRuntimePackedRead.dataHeap_at _ _ hid, PSTRRuntimePackedRead.dataHeap_at _ _ hid]
    exact congrArg BitVec.toNat (hframe _ (by simpa only [Nat.add_assoc] using hphysical))

theorem heapRepresents_of_prefix_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords base : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration old)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (hframe : ∀ physical < base, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    HeapRepresents q full capWords configuration fresh := by
  have hlogical (address : Nat) (ha : address < capWords + (2 + (staticMetadata q full).length)) :
      logicalHeap q capWords fresh address = logicalHeap q capWords old address :=
    logical_frame old fresh capWords _ base address hb hq hr hroom hbase hframe ha
  dsimp only [HeapRepresents] at rep ⊢
  obtain ⟨ht, hc, hp, hbits, hstage, hfailed, hmetadata, hused, htable⟩ := rep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframe 0 (by omega)]; exact ht
  · rw [hframe 1 (by omega)]; exact hc
  · rw [hframe 2 (by omega)]; exact hp
  · rw [hframe 3 (by omega)]; exact hbits
  · exact (hlogical capWords (by omega)).trans hstage
  · exact (hlogical (capWords + 1) (by omega)).trans hfailed
  · intro position hposition
    exact (hlogical (capWords + 2 + position) (by omega)).trans (hmetadata position hposition)
  · intro tool
    have ht := tool.isLt
    exact (hlogical _ (by omega)).trans (hused tool)
  · intro hpositive
    have hsize : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
      simp only [treeSize, ne_of_gt hq, ite_false]
    refine ⟨?_, ?_⟩
    · apply PA17RequestPaths016.physicalTableCorrect_of_frame q full _ _ (htable hpositive).1
      intro address ha
      have hsmall : address < tableWords full.length q (treeSize q full) := by
        simpa only [hsize] using ha
      exact hlogical address (by omega)
    · intro address ha
      rw [hlogical address (by omega)]
      exact (htable hpositive).2 address ha

theorem spill_represents {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords base : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base) :
    HeapRepresents q full capWords configuration (spillHeap base state) := by
  apply heapRepresents_of_prefix_frame full configuration capWords base state.heap _ hb hq rep bitmap hr hroom hbase
  intro physical hp
  exact spill_frame base state hroom physical
    (hp.trans ((Nat.le_add_right base 3).trans_lt hroom)) hp

theorem execute_represents {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords base : Nat) (state : WordState bits) (tool : Fin q)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (unused : tool ∉ configuration.used)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hf : state.register .flag = BitVec.ofNat bits base) :
    HeapRepresents q full capWords
      { configuration with stage := configuration.stage + 1, used := insert tool configuration.used }
      (executeOps rom PSTRRepairReply.program state).heap := by
  have hsp : HeapRepresents q full capWords configuration (executeOps rom spillProgram state).heap := by
    rw [spill_execute_heap rom state base hf]
    exact spill_represents full configuration capWords base state (by omega) hq rep bitmap hr hroom hbase
  rw [PSTRRepairReply.program, executeOps_append, executeOps_append, restore_heap]
  exact PSTRRuntimeRepair.execute_represents rom full configuration capWords
    (executeOps rom spillProgram state) tool hb hq hw hsp unused bitmap hr hi hnext
    (by rw [spill_address]; exact haddress) (by rw [spill_width]; exact hwidth)

theorem actual_error {bits q : Nat} (rom : PhysicalROM) (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords base : Nat) (state : WordState bits) (tool : Fin q)
    (hlaminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (hchoose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩
      configuration.used).tool = some tool)
    (hb : 8 ≤ bits) (hq : 0 < q) (hw : CapacityBits.width q ≤ bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hi : ∀ offset < 2 + (staticMetadata q full).length,
      Fits bits (4 + packedCapacityWords q capWords bits + offset))
    (hnext : Fits bits (configuration.stage + 1))
    (hroom : Fits bits (base + 3))
    (hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ base)
    (haddress : (state.register .address).toNat = tableWords full.length q (treeSize q full) + tool.val)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom PSTRRepairReply.program 40 state
    after.halted = true ∧ HeapRepresents q full capWords
      (nextConfiguration q full configuration .error) after.heap ∧ ReplyRegisters state after := by
  have unused : tool ∉ configuration.used :=
    ((PSTRCallback.callback_stage q full hlaminar ⟨configuration.stage, allowed.2⟩
      configuration.used).2.2.2 tool hchoose).2.1
  have haddr : (state.register .address).toNat < capWords := by
    rw [haddress]
    have ht := tool.isLt
    omega
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q) :=
    (Nat.mul_lt_mul_of_pos_right haddr hwp).trans
      ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt hr)
  have hword : (state.register .address).toNat * CapacityBits.width q / bits <
      packedCapacityWords q capWords bits :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < bits)).mpr
      ((Nat.mul_lt_mul_of_pos_right haddr hwp).trans_le (packedCapacityWords_mul_bits q capWords (by omega)))
  have hc : nextConfiguration q full configuration .error =
      { configuration with stage := configuration.stage + 1, used := insert tool configuration.used } := by
    have hs : configuration.stage < full.length + 1 := by have hh := allowed.2; omega
    simp only [nextConfiguration, hs, dite_true, hchoose]
    have hf := allowed.1
    cases configuration
    simp_all only
  have hreply := PSTRRepairReply.actual_reply rom state base (packedCapacityWords q capWords bits)
    hb hw hf hwidth rep.2.2.2.1 rep.2.2.1 hstart hroom (by omega) (by omega) hp ha
  dsimp only at hreply ⊢
  refine ⟨hreply.1, ?_, hreply.2⟩
  rw [show 40 = PSTRRepairReply.program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ PSTRRepairReply.program_straight
      (PSTRRepairReply.code_fit hb) (PSTRRepairReply.pc_fit hb) hp ha, hc]
  exact execute_represents rom full configuration capWords base state tool hb hq hw rep unused
    bitmap hr hi hnext hroom hbase haddress hwidth hf

theorem replyCorrect_of_registers {bits q : Nat} (capWords : Nat) (before after : WordState bits)
    (hr : ReplyRegisters before after) (answer : IndexedQuery.Reply q)
    (hc : ReplyCorrect q answer (replyState q capWords before)) :
    ReplyCorrect q answer (replyState q capWords after) := by
  obtain ⟨hv, ho, hf, hi⟩ := hr
  simpa only [ReplyCorrect, replyState, hv, ho, hf, hi] using hc

end PaperProofs.Structure.LaminarTree.PSTRRepairHeap
