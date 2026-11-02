module

public import Structure.PSTR_ReplyCapacity_025
public import Structure.PSTR_RepairSafety_021

/-! Actual access/fetch safety of the unique-HALT reply-preserving repair.
Every concrete spill and restore access is checked; the actual scratch/header
frames discharge the intervening repair's entry conditions. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRReplySafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims RawTreePreprocessingClaims PSTRReplySpill

set_option maxRecDepth 10000 in
theorem spill_access {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base heapWords : Nat) (hf : state.register .flag = BitVec.ofNat bits base)
    (hroom : Fits bits (base + 3)) (hheap : base + 3 < heapWords)
    (count : Nat) (hc : count < spillProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (spillProgram.take count) state) spillProgram[count] := by
  have h0 : Fits bits base := by simpa only [Nat.add_zero] using slot_fit base hroom 0 (by decide)
  have h1 := slot_fit base hroom 1 (by decide)
  have h2fit := slot_fit base hroom 2 (by decide)
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  change count < 8 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [spillProgram, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, hf, BitVec.ofNat_add_ofNat, h2, h3, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2fit, Nat.mod_eq_of_lt hroom]
  all_goals omega

set_option maxRecDepth 10000 in
theorem restore_access {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base heapWords : Nat) (hf : state.register .flag = BitVec.ofNat bits (base + 3))
    (hroom : Fits bits (base + 3)) (hheap : base + 3 < heapWords)
    (count : Nat) (hc : count < restoreProgram.length) :
    packingAccessFits rom heapWords (executeOps rom (restoreProgram.take count) state) restoreProgram[count] := by
  have hthree : 3 < 2 ^ bits := (Nat.le_add_left 3 base).trans_lt hroom
  have h0 : Fits bits base := by simpa only [Nat.add_zero] using slot_fit base hroom 0 (by decide)
  have h1 := slot_fit base hroom 1 (by decide)
  have h2fit := slot_fit base hroom 2 (by decide)
  have hsub : base + 3 - 3 = base := by omega
  have h2 : base + 1 + 1 = base + 2 := by omega
  have h3 : base + 2 + 1 = base + 3 := by omega
  change count < 10 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [restoreProgram, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hroom, Nat.mod_eq_of_lt hthree,
    hsub, BitVec.ofNat_add_ofNat, h2, h3,
    Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2fit]
  all_goals omega

theorem access_prefix {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed heapWords : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hp : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3)) (hheap : base + 3 < heapWords)
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base)
    (hstage : 4 + packed < base)
    (count : Nat) (hc : count < PSTRRepairReply.program.length) :
    packingAccessFits rom heapWords
      (executeOps rom (PSTRRepairReply.program.take count) state) PSTRRepairReply.program[count] := by
  have hmidlen : (spillProgram ++ PSTRRuntimeRepair.program).length = 29 := rfl
  have htotal : count < ((spillProgram ++ PSTRRuntimeRepair.program) ++ restoreProgram).length := hc
  change packingAccessFits rom heapWords
    (executeOps rom (((spillProgram ++ PSTRRuntimeRepair.program) ++ restoreProgram).take count) state)
    ((spillProgram ++ PSTRRuntimeRepair.program) ++ restoreProgram)[count]
  by_cases hfirst : count < spillProgram.length
  · have hm : count < (spillProgram ++ PSTRRuntimeRepair.program).length := by
      rw [hmidlen]
      rw [spill_length] at hfirst
      omega
    rw [List.take_append_of_le_length hm.le, List.getElem_append_left hm,
      List.take_append_of_le_length hfirst.le, List.getElem_append_left hfirst]
    exact spill_access rom state base heapWords hf hroom hheap count hfirst
  · by_cases hmiddle : count < (spillProgram ++ PSTRRuntimeRepair.program).length
    · have hsfull : spillProgram.length ≤ count := by omega
      have hright : count - spillProgram.length < PSTRRuntimeRepair.program.length := by
        rw [hmidlen] at hmiddle
        rw [spill_length, PSTRRuntimeRepair.program_length]
        omega
      have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
      have htwo : Fits bits 2 := by unfold Fits; omega
      have hthree : Fits bits 3 := by unfold Fits; omega
      have hbelow : 3 < base :=
        ((show 3 ≤ 4 by decide).trans (Nat.le_add_right 4
          ((state.register .address).toNat * CapacityBits.width q / bits))).trans_lt hmark
      have hheader3 : ((executeOps rom spillProgram state).heap (BitVec.ofNat bits 3)).toNat = bits := by
        rw [spill_execute_heap rom state base hf, spill_frame base state hroom 3 hthree hbelow]
        exact hh
      have hheader2 : ((executeOps rom spillProgram state).heap (BitVec.ofNat bits 2)).toNat = packed := by
        rw [spill_execute_heap rom state base hf, spill_frame base state hroom 2 htwo (by omega)]
        exact hp
      have hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits) :=
        hmark.trans ((Nat.le_add_right base 3).trans_lt hroom)
      have hstfit : Fits bits (4 + packed) := hstage.trans ((Nat.le_add_right base 3).trans_lt hroom)
      rw [List.take_append_of_le_length hmiddle.le, List.getElem_append_left hmiddle,
        List.take_append, List.take_of_length_le hsfull, executeOps_append, List.getElem_append_right hsfull]
      apply PSTRRepairSafety.repair_access rom (executeOps rom spillProgram state) heapWords packed hb hw
        (by rw [spill_width]; exact hwidth) hheader3 hheader2
        (by rw [spill_address]; exact hs)
        (by rw [spill_address]; exact hptr)
        (by rw [spill_address]; exact hmark.trans ((Nat.le_add_right base 3).trans_lt hheap))
        hstfit (hstage.trans ((Nat.le_add_right base 3).trans_lt hheap)) _ hright
    · have hmfull : (spillProgram ++ PSTRRuntimeRepair.program).length ≤ count := by omega
      have hright : count - (spillProgram ++ PSTRRuntimeRepair.program).length < restoreProgram.length := by
        rw [hmidlen, restore_length]
        rw [PSTRRepairReply.program_length] at hc
        omega
      have hcursor : (executeOps rom (spillProgram ++ PSTRRuntimeRepair.program) state).register .flag =
          BitVec.ofNat bits (base + 3) := by
        rw [executeOps_append]
        exact PSTRRepairReply.execute_middle_cursor rom state base hf
      rw [List.take_append, List.take_of_length_le hmfull, executeOps_append, List.getElem_append_right hmfull]
      exact restore_access rom _ base heapWords hcursor hroom hheap _ hright

theorem actual_path {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (base packed heapWords : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hf : state.register .flag = BitVec.ofNat bits base)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hpacked : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hroom : Fits bits (base + 3)) (hheap : base + 3 < heapWords)
    (hmark : 4 + (state.register .address).toNat * CapacityBits.width q / bits < base)
    (hstage : 4 + packed < base)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∀ count < 40,
      let current := packingRun rom PSTRRepairReply.program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode PSTRRepairReply.program).length ∧
      match PackingOp.decode (fetch PSTRRepairReply.program current) with
      | none => fetch PSTRRepairReply.program current = haltWords
      | some op => packingAccessFits rom heapWords current op :=
  PSTRUpdateSafety.straight_path rom PSTRRepairReply.program state heapWords PSTRRepairReply.program_straight
    (PSTRRepairReply.code_fit hb) (PSTRRepairReply.pc_fit hb) hp ha
    (access_prefix rom state base packed heapWords hb hw hf hwidth hh hpacked hs hroom hheap hmark hstage)

theorem actual_call_cost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) : callCost q full PSTRRepairReply.program command 40 heap ≤ 689 := by
  have ht := PSTRRepairReply.actual_trace_bound (callInput q full command) (packingInitial heap)
  unfold callCost
  rw [PSTRRepairReply.code_length]
  omega

end PaperProofs.Structure.LaminarTree.PSTRReplySafety
