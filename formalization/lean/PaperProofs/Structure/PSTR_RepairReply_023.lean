module

public import PaperProofs.Structure.PSTR_ReplySpill_022

/-! The old reply survives one actual contiguous spill/repair/restore
program. Scratch separation and finite-word room are numeric layout facts;
the intervening heap frame is proved from the actual marker and stage store. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRepairReply

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PSTRReplySpill

def program : List PackingOp :=
  spillProgram ++ PSTRRuntimeRepair.program ++ restoreProgram

theorem program_length : program.length = 39 := rfl

theorem program_straight : StraightProgram program := by
  intro op ho
  rcases List.mem_append.mp ho with hl | hr
  · rcases List.mem_append.mp hl with hs | hm
    · exact spill_straight op hs
    · exact PSTRRuntimeRepair.program_straight op hm
  · exact restore_straight op hr

theorem code_length : (packingCode program).length = 200 := by
  rw [packingCode_length, program_length]

set_option maxRecDepth 10000 in
theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, spillProgram, restoreProgram, PSTRRuntimeRepair.program,
    PSTRRuntimeMarkUsed.program, PSTRRuntimeAdvance.program, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 195 < 2 ^ bits
  omega

theorem execute_middle_heap {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hp : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base) :
    (executeOps rom PSTRRuntimeRepair.program (executeOps rom spillProgram state)).heap =
      PSTRRuntimeAdvance.bumpHeap packed (PSTRRuntimeMarkUsed.markHeap
        ((state.register .address).toNat * CapacityBits.width q) (spillHeap base state)) := by
  let spilled := executeOps rom spillProgram state
  let marked := executeOps rom PSTRRuntimeMarkUsed.program spilled
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have htwo : Fits bits 2 := by unfold Fits; omega
  have hthree : Fits bits 3 := by unfold Fits; omega
  have hbelow : 3 < base :=
    ((show 3 ≤ 4 by decide).trans (Nat.le_add_right 4
      ((state.register .address).toNat * CapacityBits.width q / bits))).trans_lt hmark
  have hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits) :=
    hmark.trans ((Nat.le_add_right base 3).trans_lt hroom)
  have hsp : spilled.heap = spillHeap base state := spill_execute_heap rom state base hf
  have hheader3 : (spilled.heap (BitVec.ofNat bits 3)).toNat = bits := by
    rw [hsp, spill_frame base state hroom 3 hthree hbelow]
    exact hh
  have hheader2 : (spilled.heap (BitVec.ofNat bits 2)).toNat = packed := by
    rw [hsp, spill_frame base state hroom 2 htwo (by omega)]
    exact hp
  have hm : marked.heap = PSTRRuntimeMarkUsed.markHeap
      ((state.register .address).toNat * CapacityBits.width q) spilled.heap := by
    dsimp only [marked]
    rw [PSTRRuntimeMarkUsed.execute_heap rom spilled (by omega) hw
      (by rw [spill_width]; exact hwidth) hheader3
      (by rw [spill_address]; exact hs), spill_address]
  have hmheader : (marked.heap (BitVec.ofNat bits 2)).toNat = packed := by
    rw [hm, PSTRRuntimeMarkUsed.markHeap_header _ spilled.heap hb hptr 2 (by decide)]
    exact hheader2
  rw [PSTRRuntimeRepair.program, executeOps_append,
    PSTRRuntimeAdvance.execute_heap rom marked packed hmheader, hm, hsp]

theorem execute_middle_cursor {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base : Nat) (hf : state.register .flag = BitVec.ofNat bits base) :
    (executeOps rom PSTRRuntimeRepair.program (executeOps rom spillProgram state)).register .flag =
      BitVec.ofNat bits (base + 3) := by
  rw [repair_cursor, spill_cursor rom state base hf]

theorem execute_middle_slots {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hp : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base)
    (hstage : 4 + packed < base) (offset : Nat) (ho : offset < 4) :
    (executeOps rom PSTRRuntimeRepair.program (executeOps rom spillProgram state)).heap
      (BitVec.ofNat bits (base + offset)) = savedWord state offset := by
  have hslot := slot_fit base hroom offset (by omega)
  have hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits) :=
    hmark.trans ((Nat.le_add_right base 3).trans_lt hroom)
  have hstfit : Fits bits (4 + packed) := hstage.trans ((Nat.le_add_right base 3).trans_lt hroom)
  have hnmark : BitVec.ofNat bits (base + offset) ≠
      BitVec.ofNat bits (4 + (state.register .address).toNat * CapacityBits.width q / bits) :=
    (ofNat_injective_of_fit _ _ hslot hptr).not.mpr (by omega)
  have hnstage : BitVec.ofNat bits (base + offset) ≠ BitVec.ofNat bits (4 + packed) :=
    (ofNat_injective_of_fit _ _ hslot hstfit).not.mpr (by omega)
  rw [execute_middle_heap rom state base packed hb hw hf hwidth hh hp hs hroom hmark,
    PSTRRuntimeAdvance.heap_frame _ _ _ hnstage, PSTRRuntimeMarkUsed.markHeap_frame _ _ _ hnmark]
  exact spill_slot base state hroom offset ho

theorem execute_reply {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hp : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base)
    (hstage : 4 + packed < base) :
    ReplyRegisters state (executeOps rom program state) := by
  rw [program, executeOps_append, executeOps_append]
  exact restore_reply rom state _ base hb hroom (execute_middle_cursor rom state base hf)
    (execute_middle_slots rom state base packed hb hw hf hwidth hh hp hs hroom hmark hstage)

theorem actual_reply {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hpacked : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3))
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base)
    (hstage : 4 + packed < base)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 40 state
    after.halted = true ∧ ReplyRegisters state after := by
  dsimp only
  rw [show 40 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
  exact ⟨rfl, execute_reply rom state base packed hb hw hf hwidth hh hpacked hs hroom hmark hstage⟩

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 40 state).length ≤ 480 :=
  packingDynamicTrace_length_le rom program 40 state

end PaperProofs.Structure.LaminarTree.PSTRRepairReply
