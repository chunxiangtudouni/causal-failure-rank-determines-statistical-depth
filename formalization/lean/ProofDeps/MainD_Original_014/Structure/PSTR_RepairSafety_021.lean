module

public import Structure.PSTR_UpdateSafety_020

/-! Concrete all-prefix physical accesses for the fixed used-bit marker and
the single contiguous mark-then-advance program. Real header preservation
discharges the second block's entry condition. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRepairSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims RawTreePreprocessingClaims

set_option maxRecDepth 10000 in
theorem mark_access {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits))
    (hheap : 4 + (state.register .address).toNat * CapacityBits.width q / bits < heapWords)
    (count : Nat) (hc : count < PSTRRuntimeMarkUsed.program.length) :
    packingAccessFits rom heapWords
      (executeOps rom (PSTRRuntimeMarkUsed.program.take count) state)
      PSTRRuntimeMarkUsed.program[count] := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hstart : start < 2 ^ bits := hs
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hthree : 3 < 2 ^ bits := by omega
  have hwidthFit : CapacityBits.width q < 2 ^ bits := hw.trans_lt hbits
  have hdiv : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hstart
  have hphysical : 4 + start / bits < 2 ^ bits := hptr
  have haccess : 4 + start / bits < heapWords := hheap
  have hheaderAccess : 3 < heapWords :=
    ((show 3 ≤ 4 by decide).trans (Nat.le_add_right 4 (start / bits))).trans_lt haccess
  have hcomm : start / bits + 4 = 4 + start / bits := by omega
  change count < 13 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [PSTRRuntimeMarkUsed.program, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, hwidth, PSTRRuntimePackedRead.header_word state hh,
    arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
    Nat.mod_eq_of_lt hbits, Nat.mod_eq_of_lt hthree, Nat.mod_eq_of_lt hwidthFit,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hstart, Nat.mod_eq_of_lt hdiv, hcomm, Nat.mod_eq_of_lt hphysical]
  all_goals first | exact hheaderAccess | omega

theorem repair_access {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hpacked : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits))
    (hheap : 4 + (state.register .address).toNat * CapacityBits.width q / bits < heapWords)
    (hstage : Fits bits (4 + packed)) (hstageHeap : 4 + packed < heapWords)
    (count : Nat) (hc : count < PSTRRuntimeRepair.program.length) :
    packingAccessFits rom heapWords
      (executeOps rom (PSTRRuntimeRepair.program.take count) state)
      PSTRRuntimeRepair.program[count] := by
  have htotal : count < (PSTRRuntimeMarkUsed.program ++ PSTRRuntimeAdvance.program).length := hc
  change packingAccessFits rom heapWords
    (executeOps rom ((PSTRRuntimeMarkUsed.program ++ PSTRRuntimeAdvance.program).take count) state)
    (PSTRRuntimeMarkUsed.program ++ PSTRRuntimeAdvance.program)[count]
  by_cases hleft : count < PSTRRuntimeMarkUsed.program.length
  · rw [List.take_append_of_le_length hleft.le,
      List.getElem_append_left hleft]
    exact mark_access rom state heapWords hb hw hwidth hh hs hptr hheap count hleft
  · have hn : PSTRRuntimeMarkUsed.program.length ≤ count := by omega
    have hright : count - PSTRRuntimeMarkUsed.program.length < PSTRRuntimeAdvance.program.length := by
      rw [PSTRRuntimeRepair.program_length] at hc
      rw [PSTRRuntimeMarkUsed.program_length, PSTRRuntimeAdvance.program_length]
      have hlen := PSTRRuntimeMarkUsed.program_length
      omega
    have hmid : ((executeOps rom PSTRRuntimeMarkUsed.program state).heap
        (BitVec.ofNat bits 2)).toNat = packed := by
      rw [PSTRRuntimeMarkUsed.execute_heap rom state (by omega) hw hwidth hh hs,
        PSTRRuntimeMarkUsed.markHeap_header _ state.heap hb hptr 2 (by decide)]
      exact hpacked
    rw [List.take_append, List.take_of_length_le hn,
      executeOps_append, List.getElem_append_right hn]
    exact PSTRUpdateSafety.advance_access rom (executeOps rom PSTRRuntimeMarkUsed.program state)
      heapWords packed hb hmid hstage hstageHeap _ hright

theorem repair_path {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hpacked : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hptr : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits))
    (hheap : 4 + (state.register .address).toNat * CapacityBits.width q / bits < heapWords)
    (hstage : Fits bits (4 + packed)) (hstageHeap : 4 + packed < heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∀ count < 22,
      let current := packingRun rom PSTRRuntimeRepair.program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode PSTRRuntimeRepair.program).length ∧
      match PackingOp.decode (fetch PSTRRuntimeRepair.program current) with
      | none => fetch PSTRRuntimeRepair.program current = haltWords
      | some op => packingAccessFits rom heapWords current op :=
  PSTRUpdateSafety.straight_path rom PSTRRuntimeRepair.program state heapWords
    PSTRRuntimeRepair.program_straight (PSTRRuntimeRepair.code_fit hb) (PSTRRuntimeRepair.pc_fit hb)
    hp ha (repair_access rom state heapWords packed hb hw hwidth hh hpacked hs hptr hheap hstage hstageHeap)

end PaperProofs.Structure.LaminarTree.PSTRRepairSafety
