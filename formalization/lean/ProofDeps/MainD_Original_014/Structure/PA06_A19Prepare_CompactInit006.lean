module

public import PaperProofs.Structure.RawCandidateConstructorPrefix
public import PaperProofs.Structure.RawCandidateWorkspaceInitWord
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000

/-! PRIVATE UNCOMPILED bounded compact initializer.
Only original op9 changes: multiply flag flag index becomes constant flag0.
The code still computes M and the temporary M*q from actual raw headers.
It writes only heap8=16 and heap16=M. No matrix or precomputed M is supplied.
This does not claim an entire compact tree constructor or packed output. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactInit006

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open RawCandidateWorkspaceInit (candidateCount candidateCount_fits workspaceBase_fits)

/-- Exact original16-op body with only zero-based instruction9 replaced. -/
def initProgram : List PackingOp :=
  [.base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .old .index)),
   .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .fresh .index)),
   .base (.base (.add .total .old .fresh)),
   .base (.base (.constant .index 1)),
   .base (.base (.add .total .total .index)),
   .arithmetic .multiply .flag .total .fresh,
   .base (.base (.constant .index 8)),
   .base (.base (.constant .flag 0)),
   .base (.base (.constant .index 16)),
   .base (.base (.add .flag .flag .index)),
   .base (.base (.constant .address 8)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.minimum .address .flag .flag)),
   .base (.base (.storeHeap .address .total))]

theorem initProgram_eq_old_set : initProgram = RawCandidateWorkspaceInit.program.set 9
    (.base (.base (.constant .flag 0))) := rfl

theorem initProgram_length : initProgram.length = 16 := rfl

theorem initProgram_noJump : ∀ op ∈ initProgram, NoJump op := by
  simp [initProgram, NoJump]

def paddingOp : PackingOp := .base (.base (.constant .value 0))

structure Initialized (N q start : Nat) (before after : NatState) : Prop where
  base_cell : after.heap 8 = 16
  count_cell : after.heap 16 = candidateCount N q
  heap_frame : ∀ address, address ≠ 8 → address ≠ 16 → after.heap address = before.heap address
  value : after.register .value = before.register .value
  old : after.register .old = N
  fresh : after.register .fresh = q
  total : after.register .total = candidateCount N q
  flag : after.register .flag = 16
  address : after.register .address = 16
  index : after.register .index = 16
  pc : after.pc = 5 * (start + 16)
  active : after.halted = false

theorem runOps_effect (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (state : NatState) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    Initialized full.length q start state (runOps (rawIncidenceROM q full) initProgram state) := by
  constructor
  all_goals simp [initProgram, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    raw_header_N, raw_header_q, candidateCount, hpc, ha]
  all_goals first | omega | (intro address h8 h16; simp [h8, h16])

theorem append_slice (left right : List PackingOp) :
    left.length + 16 ≤ (left ++ initProgram ++ right).length ∧
      ∀ position < 16, (left ++ initProgram ++ right).getD (left.length + position) paddingOp =
        initProgram.getD position paddingOp := by
  constructor
  · simp only [List.length_append, initProgram_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ initProgram) right paddingOp _ (by
      simp only [List.length_append, initProgram_length]; omega),
      List.getD_append_right left initProgram paddingOp _ (by omega), Nat.add_sub_cancel_left]

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 16 ≤ containing.length)
  (hcode : ∀ position < 16, containing.getD (start + position) paddingOp =
    initProgram.getD position paddingOp)

include hbound hcode

theorem natRun_prefix_eq (state : NatState) (hpc : state.pc = 5 * start)
    (ha : state.halted = false) (count : Nat) (hc : count ≤ 16) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) (initProgram.take count) state := by
  have hlen : (initProgram.take count).length = count := List.length_take_of_le (by
    change count ≤ 16; exact hc)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment (rawIncidenceROM q full) containing (initProgram.take count) start
    (by rw [hlen]; omega) ?_ ?_ state hpc ha
  · intro position hp
    have hp' : position < count := by simpa only [hlen] using hp
    have hh := hcode position (by omega)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by change position < 16; omega)] at hh
    simpa only [List.getElem_take] using hh
  · intro op hop
    exact initProgram_noJump op (List.mem_of_mem_take hop)

theorem initialize_workspace (state : NatState) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    Initialized full.length q start state (natRun (rawIncidenceROM q full) containing 16 state) := by
  rw [natRun_prefix_eq q full containing start hbound hcode state hpc ha 16 le_rfl,
    show initProgram.take 16 = initProgram from by
      simpa only [initProgram_length] using (List.take_length (l := initProgram))]
  exact runOps_effect q full start state hpc ha

end Linked

theorem initialize_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    Initialized full.length q left.length state
      (natRun (rawIncidenceROM q full) (left ++ initProgram ++ right) 16 state) :=
  initialize_workspace q full _ left.length (append_slice left right).1 (append_slice left right).2 state hpc ha

/-- The original checker/dispatcher enters this fixed compact init, then
any tail, without supplying an initialized workspace or a table oracle. -/
def program (tail : List PackingOp) : List PackingOp := dispatcherProgram (initProgram ++ tail)

theorem initialized_entry (tail : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (hl : LaminarSchedule full) :
    ∃ clock : Nat, clock ≤ checkerSteps full.length q + 17 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).halted = false ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).pc = 5 * (checker.length + 18) ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).register .value = 1 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 8 = 16 ∧
      (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap 16 = candidateCount full.length q ∧
      ∀ address : Nat, 8 ≤ address → address ≠ 8 → address ≠ 16 →
        (natRun (rawIncidenceROM q full) (program tail) clock natInitial).heap address = 0 := by
  let front := checker ++ dispatcherGate (initProgram ++ tail).length
  have hfront : front.length = checker.length + 2 := by
    simp only [front, List.length_append, dispatcherGate_length]
  have hprogram : front ++ initProgram ++ tail = program tail := by
    simp only [front, program, dispatcherProgram, List.append_assoc]
  obtain ⟨clock, hc, ha, hp, hv, hz⟩ := dispatcher_constructor_entry (initProgram ++ tail) q full hl
  let before := natRun (rawIncidenceROM q full) (program tail) clock natInitial
  have hbpc : before.pc = 5 * front.length := by rw [hfront]; exact hp
  have hi := initialize_append q full front tail before hbpc ha
  rw [hprogram] at hi
  have hi' : Initialized full.length q front.length before
      (natRun (rawIncidenceROM q full) (program tail) (clock + 16) natInitial) := by
    simpa only [before, natRun_add] using hi
  refine ⟨clock + 16, by omega, hi'.active, ?_, hi'.value.trans hv, hi'.base_cell, hi'.count_cell, ?_⟩
  · rw [hi'.pc, hfront]
  · intro address haddress h8 h16
    rw [hi'.heap_frame address h8 h16]
    exact hz address haddress

/-- Every actual init access is below17: writable addresses are exactly8
and16, while only raw-ROM header0/1 are read. M*q is register-only. -/
theorem runOps_prefix_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (state : NatState) (count : Nat) (hc : count < 16) :
    NatAccessFits (rawIncidenceROM q full) 17 (runOps (rawIncidenceROM q full)
      (initProgram.take count) state) (initProgram.getD count paddingOp) := by
  interval_cases count <;>
    simp +decide [initProgram, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic]

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases he : reg = target
  · simpa only [he, Function.update_self] using hv
  · simpa only [Function.update_of_ne he] using hf reg

theorem runOps_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (count : Nat) (hc : count ≤ 16) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full)
      (initProgram.take count) state) := by
  have hM := candidateCount_fits full.length q
  have hdim (value : Nat) (hv : value ≤ candidateCount full.length q) : Fits (indexWidth 16 full.length q) value :=
    hv.trans_lt hM
  have hN : Fits (indexWidth 16 full.length q) full.length := hdim _ (by unfold candidateCount; omega)
  have hq : Fits (indexWidth 16 full.length q) q := hdim _ (by unfold candidateCount; omega)
  have hsum : Fits (indexWidth 16 full.length q) (full.length + q) := hdim _ (by unfold candidateCount; omega)
  have hMQ : Fits (indexWidth 16 full.length q) ((full.length + q + 1) * q) := by
    apply lt_of_le_of_lt _ (workspaceBase_fits full.length q)
    unfold RawCandidateWorkspaceInit.workspaceBase candidateCount
    nlinarith
  have hconstant (value : Nat) (hv : value ≤ 16) : Fits (indexWidth 16 full.length q) value :=
    (hv.trans (RawCandidateWorkspaceInit.workspaceBase_ge full.length q)).trans_lt (workspaceBase_fits full.length q)
  have hzero := hconstant 0 (by decide)
  have hone := hconstant 1 (by decide)
  have height := hconstant 8 (by decide)
  have hsixteen := hconstant 16 le_rfl
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hlt : count < 16 := by omega
    have hprev := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 16; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (initProgram[count]'(by change count < 16; exact hlt))
      (runOps _ (initProgram.take count) state))
    interval_cases count <;>
      simp only [initProgram, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
        natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hprev | apply fits_update hprev
    · exact hzero
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N] using hN
    · exact hone
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_q] using hq
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q] using hsum
    · exact hone
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q, candidateCount] using hM
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, raw_header_N, raw_header_q] using hMQ
    · exact height
    · exact hzero
    · exact hsixteen
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute] using hsixteen
    · exact height
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute] using hsixteen

section WordLinked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 16 ≤ containing.length)
  (hcode : ∀ position < 16, containing.getD (start + position) paddingOp = initProgram.getD position paddingOp)

include hbound hcode

theorem natRun_prefix_pc (state : NatState) (hpc : state.pc = 5 * start)
    (ha : state.halted = false) (count : Nat) (hc : count ≤ 16) :
    (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + count) := by
  rw [natRun_prefix_eq q full containing start hbound hcode state hpc ha count hc,
    runOps_pc _ _ _ (fun op hop => initProgram_noJump op (List.mem_of_mem_take hop)),
    List.length_take_of_le (by change count ≤ 16; exact hc), hpc]
  omega

theorem word_run_eq_nat (state : NatState) (hpc : state.pc = 5 * start)
    (ha : state.halted = false) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ 16) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  constructor
  · rw [natRun_prefix_eq q full containing start hbound hcode state hpc ha k (by omega)]
    exact runOps_prefix_registersFit q full state hf k (by omega)
  · rw [natRun_prefix_pc q full containing start hbound hcode state hpc ha k (by omega)]
    exact lt_of_le_of_lt (by omega) hend

/-- This local word prefix needs only17 allocated heap words. Generic
retention/order/parent arrays and packed output are separate later phases. -/
theorem word_prefix_accessFits (state : NatState) (hpc : state.pc = 5 * start)
    (ha : state.halted = false) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count < 16) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    packingAccessFits (rawIncidenceROM q full) 17 after (initProgram.getD count paddingOp) := by
  rw [word_run_eq_nat q full containing start hbound hcode state hpc ha hf hend hwords count hc.le]
  have hreg : RegistersFit (indexWidth 16 full.length q)
      (natRun (rawIncidenceROM q full) containing count state) := by
    rw [natRun_prefix_eq q full containing start hbound hcode state hpc ha count hc.le]
    exact runOps_prefix_registersFit q full state hf count hc.le
  apply physical_access_of_nat _ 17 _ _ hreg
  rw [natRun_prefix_eq q full containing start hbound hcode state hpc ha count hc.le]
  exact runOps_prefix_accessFits q full state count hc

end WordLinked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactInit006
