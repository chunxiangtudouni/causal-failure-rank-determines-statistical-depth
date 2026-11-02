module

public import PaperProofs.Structure.RawCandidateWorkspaceBounds
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawIncidenceOuterSafety
import Mathlib.Tactic.IntervalCases

/-! Actual word execution and every-prefix safety of the existing fixed
sixteen-op initializer.  Only initial register Fits and caller code/PC
linking conditions are assumed.  B/M, writes, and safe accesses are proved
from the original raw header, including q=0. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceInitWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateWorkspaceInit RawCandidateWorkspaceBounds

abbrev body := RawCandidateWorkspaceInit.program
abbrev paddingOp := RawCandidateWorkspaceInit.paddingOp

private theorem fits_register_update {bits : Nat} {registers : Register → Nat}
    (hfit : ∀ register, Fits bits (registers register)) (target : Register) (value : Nat)
    (hvalue : Fits bits value) :
    ∀ register, Fits bits (Function.update registers target value register) := by
  intro register
  by_cases heq : register = target
  · simpa only [heq, Function.update_self] using hvalue
  · simpa only [Function.update_of_ne heq] using hfit register

theorem runOps_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hfit : RegistersFit (indexWidth 16 full.length q) state) (count : Nat) (hcount : count ≤ 16) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (body.take count) state) := by
  have hB := workspaceBase_fits full.length q
  have hM := candidateCount_fits full.length q
  have hdim (value : Nat) (hv : value ≤ candidateCount full.length q) :
      Fits (indexWidth 16 full.length q) value := hv.trans_lt hM
  have hN : Fits (indexWidth 16 full.length q) full.length := hdim _ (by unfold candidateCount; omega)
  have hq : Fits (indexWidth 16 full.length q) q := hdim _ (by unfold candidateCount; omega)
  have hsum : Fits (indexWidth 16 full.length q) (full.length + q) := hdim _ (by unfold candidateCount; omega)
  have hMQ : Fits (indexWidth 16 full.length q) ((full.length + q + 1) * q) := by
    apply lt_of_le_of_lt _ hB
    unfold workspaceBase candidateCount
    nlinarith
  have h8MQ : Fits (indexWidth 16 full.length q) ((full.length + q + 1) * (q * 8)) := by
    apply lt_of_le_of_lt _ hB
    unfold workspaceBase candidateCount
    nlinarith
  have hfinal : Fits (indexWidth 16 full.length q) ((full.length + q + 1) * (q * 8) + 16) := by
    convert hB using 1
    unfold workspaceBase candidateCount
    ring
  have hconstant (value : Nat) (hv : value ≤ 16) : Fits (indexWidth 16 full.length q) value :=
    (hv.trans (workspaceBase_ge full.length q)).trans_lt hB
  have hzero := hconstant 0 (by decide)
  have hone := hconstant 1 (by decide)
  have height := hconstant 8 (by decide)
  have hsixteen := hconstant 16 le_rfl
  induction count with
  | zero => exact hfit
  | succ count ih =>
    have hc : count < 16 := by omega
    have hprev := ih hc.le
    rw [List.take_succ_eq_append_getElem (by change count < 16; exact hc), runOps_append]
    change RegistersFit _ (natExecuteOp _ (body[count]'(by change count < 16; exact hc))
      (runOps _ (body.take count) state))
    interval_cases count <;>
      simp only [body, RawCandidateWorkspaceInit.program, List.getElem_cons_zero,
        List.getElem_cons_succ, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hprev | apply fits_register_update hprev
    · exact hzero
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N] using hN
    · exact hone
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_q] using hq
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q] using hsum
    · exact hone
    · simpa +decide [runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q,
        candidateCount] using hM
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        raw_header_N, raw_header_q] using hMQ
    · exact height
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        raw_header_N, raw_header_q, Nat.mul_assoc] using h8MQ
    · exact hsixteen
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        raw_header_N, raw_header_q, Nat.mul_assoc] using hfinal
    · exact height
    · simpa +decide [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        raw_header_N, raw_header_q, Nat.mul_assoc] using hfinal

theorem runOps_prefix_accessFits (q : Nat) (full : List (Finset (Fin q)))
    (state : NatState) (count : Nat) (hcount : count < 16) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (body.take count) state) (body.getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have hM := candidateCount_pos full.length q
  interval_cases count <;>
    simp +decide [body, RawCandidateWorkspaceInit.program, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits,
      rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic, workspaceLimit, workspaceBase, candidateCount,
      Nat.mul_comm]
  all_goals nlinarith

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 16 ≤ containing.length)
  (hcode : ∀ position < 16, containing.getD (start + position) paddingOp = body.getD position paddingOp)

include hbound hcode

theorem natRun_prefix_eq (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (count : Nat) (hcount : count ≤ 16) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) (body.take count) state := by
  have hlen : (body.take count).length = count := List.length_take_of_le (by change count ≤ 16; exact hcount)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment (rawIncidenceROM q full) containing (body.take count) start
    (by rw [hlen]; omega) ?_ ?_ state hpc hactive
  · intro position hp
    have hp' : position < count := by simpa only [hlen] using hp
    have hh := hcode position (by omega)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by change position < 16; omega)] at hh
    simpa only [List.getElem_take] using hh
  · intro op hop
    exact program_noJump op (List.mem_of_mem_take hop)

theorem natRun_prefix_pc (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (count : Nat) (hcount : count ≤ 16) :
    (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + count) := by
  rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount,
    runOps_pc _ _ _ (fun op hop => program_noJump op (List.mem_of_mem_take hop)),
    List.length_take_of_le (by change count ≤ 16; exact hcount), hpc]
  omega

theorem natRun_prefix_safe (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (count : Nat) (hcount : count ≤ 16) :
    RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
        (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  refine ⟨?_, ?_, ?_⟩
  · rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount]
    exact runOps_prefix_registersFit q full state hfit count hcount
  · rw [natRun_prefix_pc q full containing start hbound hcode state hpc hactive count hcount]
    exact lt_of_le_of_lt (by omega) hend
  · rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount,
      runOps_halted, hactive]

theorem word_run_eq_nat (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hcount : count ≤ 16) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode state hpc hactive hfit hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hcount : count < 16) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat = 5 * (start + count) ∧
      after.pc.toNat + 4 < (packingCode containing).length ∧
      PackingOp.decode (fetch containing after) = some (body.getD count paddingOp) ∧
      packingAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) after (body.getD count paddingOp) := by
  have hs := natRun_prefix_safe q full containing start hbound hcode state hpc hactive hfit hend count hcount.le
  have hpcNat := natRun_prefix_pc q full containing start hbound hcode state hpc hactive count hcount.le
  have hword := word_run_eq_nat q full containing start hbound hcode state hpc hactive hfit hend hwords count hcount.le
  dsimp only
  rw [hword]
  have hpcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord
      (indexWidth 16 full.length q)).pc.toNat = 5 * (start + count) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1, hpcNat]
  refine ⟨hs.2.2, hpcWord, ?_, ?_, ?_⟩
  · rw [hpcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1, physicalFetch_eq _ _ _ hwords, hpcNat]
    change PackingOp.decode (natFetch containing (5 * (start + count))) = _
    rw [natFetch_body containing (start + count) (by omega), decode_encode]
    have hh := hcode count hcount
    rw [List.getD_eq_getElem _ _ (by omega)] at hh
    exact congrArg some hh
  · apply physical_access_of_nat _ (workspaceLimit full.length q) _ _ hs.1
    rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount.le]
    exact runOps_prefix_accessFits q full state count hcount

theorem word_prefix_values (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hcount : count ≤ 16) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    (∀ register, (after.register register).toNat =
      (natRun (rawIncidenceROM q full) containing count state).register register) ∧
      after.pc.toNat = 5 * (start + count) ∧ after.halted = false := by
  have hs := natRun_prefix_safe q full containing start hbound hcode state hpc hactive hfit hend count hcount
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode state hpc hactive hfit hend hwords count hcount]
  refine ⟨fun register => toWord_register_toNat _ _ hs.1 register, ?_, hs.2.2⟩
  change (BitVec.ofNat _ _).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs.2.1,
    natRun_prefix_pc q full containing start hbound hcode state hpc hactive count hcount]

structure WordInitialized (N q start : Nat) (before after : WordState (indexWidth 16 N q)) : Prop where
  base_cell : (after.heap (BitVec.ofNat (indexWidth 16 N q) 8)).toNat = workspaceBase N q
  count_cell : (after.heap (BitVec.ofNat (indexWidth 16 N q) (workspaceBase N q))).toNat = candidateCount N q
  heap_frame : ∀ address, address ≠ BitVec.ofNat (indexWidth 16 N q) 8 →
    address ≠ BitVec.ofNat (indexWidth 16 N q) (workspaceBase N q) → after.heap address = before.heap address
  value : after.register .value = before.register .value
  old : (after.register .old).toNat = N
  fresh : (after.register .fresh).toNat = q
  total : (after.register .total).toNat = candidateCount N q
  flag : (after.register .flag).toNat = workspaceBase N q
  address : (after.register .address).toNat = workspaceBase N q
  index : (after.register .index).toNat = 16
  pc : after.pc.toNat = 5 * (start + 16)
  active : after.halted = false

theorem initialize_word (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    WordInitialized full.length q start (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) containing 16 (state.toWord (indexWidth 16 full.length q))) := by
  have hn := initialize_workspace q full containing start hbound hcode state hpc hactive
  have hB := workspaceBase_fits full.length q
  have hM := candidateCount_fits full.length q
  have h8 : Fits (indexWidth 16 full.length q) 8 :=
    (show 8 ≤ workspaceBase full.length q by have h := workspaceBase_ge full.length q; omega).trans_lt hB
  have h16 : Fits (indexWidth 16 full.length q) 16 := (workspaceBase_ge full.length q).trans_lt hB
  have hN : Fits (indexWidth 16 full.length q) full.length :=
    (show full.length ≤ candidateCount full.length q by unfold candidateCount; omega).trans_lt hM
  have hq : Fits (indexWidth 16 full.length q) q :=
    (show q ≤ candidateCount full.length q by unfold candidateCount; omega).trans_lt hM
  rw [word_run_eq_nat q full containing start hbound hcode state hpc hactive hfit hend hwords 16 le_rfl]
  constructor
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h8, hn.base_cell, Nat.mod_eq_of_lt hB]
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB, hn.count_cell, Nat.mod_eq_of_lt hM]
  · intro address hne8 hneB
    change BitVec.ofNat _ _ = BitVec.ofNat _ _
    apply congrArg (BitVec.ofNat _)
    apply hn.heap_frame address.toNat
    · intro heq
      apply hne8
      apply BitVec.eq_of_toNat_eq
      exact heq.trans (Nat.mod_eq_of_lt h8).symm
    · intro heq
      apply hneB
      apply BitVec.eq_of_toNat_eq
      exact heq.trans (Nat.mod_eq_of_lt hB).symm
  · exact congrArg (BitVec.ofNat _) hn.value
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.old, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.fresh, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.total, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.flag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.index, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h16]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend]
  · exact hn.active

end Linked

/-- The appended body is entered and returned while active; no stopped
word state is restarted. All slice hypotheses are discharged here. -/
theorem initialize_word_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (left.length + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode (left ++ body ++ right))) :
    WordInitialized full.length q left.length (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) (left ++ body ++ right) 16 (state.toWord (indexWidth 16 full.length q))) :=
  initialize_word q full _ left.length (RawCandidateWorkspaceInit.append_slice left right).1
    (RawCandidateWorkspaceInit.append_slice left right).2 state hpc hactive hfit hend hwords

theorem word_prefix_safe_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (left.length + 16)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode (left ++ body ++ right)))
    (count : Nat) (hcount : count < 16) :
    let after := packingRun (rawIncidenceROM q full) (left ++ body ++ right) count
      (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat = 5 * (left.length + count) ∧
      after.pc.toNat + 4 < (packingCode (left ++ body ++ right)).length ∧
      PackingOp.decode (fetch (left ++ body ++ right) after) = some (body.getD count paddingOp) ∧
      packingAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) after (body.getD count paddingOp) :=
  word_prefix_safe q full _ left.length (RawCandidateWorkspaceInit.append_slice left right).1
    (RawCandidateWorkspaceInit.append_slice left right).2 state hpc hactive hfit hend hwords count hcount

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceInitWord
