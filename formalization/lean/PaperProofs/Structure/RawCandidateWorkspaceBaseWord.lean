module

public import PaperProofs.Structure.RawCandidateWorkspaceBaseRAM
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawIncidenceOuterSafety
import Mathlib.Tactic.IntervalCases

/-! Actual word execution of the existing twelve-op base recovery block.
The initial heap is arbitrary, including cell 8.  Code-slice/word-width
conditions are caller linking obligations, not restrictions on raw inputs. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBaseWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateWorkspaceInit

abbrev body := RawCandidateWorkspaceBaseRAM.program
abbrev paddingOp := RawCandidateWorkspaceBaseRAM.paddingOp

private theorem fits_register_update {bits : Nat} {registers : Register → Nat}
    (hfit : ∀ register, Fits bits (registers register)) (target : Register) (value : Nat)
    (hvalue : Fits bits value) :
    ∀ register, Fits bits (Function.update registers target value register) := by
  intro register
  by_cases heq : register = target
  · simpa only [heq, Function.update_self] using hvalue
  · simpa only [Function.update_of_ne heq] using hfit register

theorem runOps_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hfit : RegistersFit (indexWidth 16 full.length q) state) (count : Nat) (hcount : count ≤ 12) :
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
    have hc : count < 12 := by omega
    have hprev := ih hc.le
    rw [List.take_succ_eq_append_getElem (by change count < 12; exact hc), runOps_append]
    change RegistersFit _ (natExecuteOp _ (body[count]'(by change count < 12; exact hc))
      (runOps _ (body.take count) state))
    interval_cases count <;>
      simp only [body, RawCandidateWorkspaceBaseRAM.program, List.getElem_cons_zero,
        List.getElem_cons_succ, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals
      apply fits_register_update hprev
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

theorem runOps_prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (heapWords : Nat)
    (state : NatState) (count : Nat) (hcount : count < 12) :
    NatAccessFits (rawIncidenceROM q full) heapWords
      (runOps (rawIncidenceROM q full) (body.take count) state)
        (body[count]'(by change count < 12; exact hcount)) := by
  interval_cases count <;>
    simp +decide [body, RawCandidateWorkspaceBaseRAM.program, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits,
      rawIncidenceROM, PhysicalROM.words]

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 12 ≤ containing.length)
  (hcode : ∀ position < 12, containing.getD (start + position) paddingOp = body.getD position paddingOp)

include hbound hcode

theorem natRun_prefix_eq (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (count : Nat) (hcount : count ≤ 12) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) (body.take count) state := by
  have hlen : (body.take count).length = count := List.length_take_of_le (by change count ≤ 12; exact hcount)
  conv_lhs => rw [← hlen]
  apply natRun_of_straight_segment (rawIncidenceROM q full) containing (body.take count) start
    (by rw [hlen]; omega) ?_ ?_ state hpc hactive
  · intro position hp
    have hp' : position < count := by simpa only [hlen] using hp
    have hh := hcode position (by omega)
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by change position < 12; omega)] at hh
    simpa only [List.getElem_take] using hh
  · intro op hop
    exact RawCandidateWorkspaceBaseRAM.program_noJump op (List.mem_of_mem_take hop)

theorem natRun_prefix_pc (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (count : Nat) (hcount : count ≤ 12) :
    (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + count) := by
  rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount,
    runOps_pc _ _ _ (fun op hop => RawCandidateWorkspaceBaseRAM.program_noJump op (List.mem_of_mem_take hop)),
    List.length_take_of_le (by change count ≤ 12; exact hcount), hpc]
  omega

theorem natRun_prefix_safe (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 12)))
    (count : Nat) (hcount : count ≤ 12) :
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
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 12)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hcount : count ≤ 12) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode state hpc hactive hfit hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 12)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (heapWords count : Nat) (hcount : count < 12) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat = 5 * (start + count) ∧
      after.pc.toNat + 4 < (packingCode containing).length ∧
      PackingOp.decode (fetch containing after) = some (body[count]'(by change count < 12; exact hcount)) ∧
      packingAccessFits (rawIncidenceROM q full) heapWords after (body[count]'(by change count < 12; exact hcount)) := by
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
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by change count < 12; exact hcount)] at hh
    exact congrArg some hh
  · apply physical_access_of_nat _ heapWords _ _ hs.1
    rw [natRun_prefix_eq q full containing start hbound hcode state hpc hactive count hcount.le]
    exact runOps_prefix_accessFits q full heapWords state count hcount

structure WordRecovered (N q start : Nat) (before after : WordState (indexWidth 16 N q)) : Prop where
  heap : after.heap = before.heap
  old : after.register .old = before.register .old
  fresh : after.register .fresh = before.register .fresh
  value : after.register .value = before.register .value
  address : (after.register .address).toNat = workspaceBase N q
  pc : after.pc.toNat = 5 * (start + 12)
  active : after.halted = false

theorem recover_word (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 12)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    WordRecovered full.length q start (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) containing 12 (state.toWord (indexWidth 16 full.length q))) := by
  have hn := RawCandidateWorkspaceBaseRAM.recover q full containing start hbound hcode state hpc hactive
  rw [word_run_eq_nat q full containing start hbound hcode state hpc hactive hfit hend hwords 12 le_rfl]
  constructor
  · exact congrArg (fun heap : Nat → Nat => fun address : BitVec (indexWidth 16 full.length q) =>
      BitVec.ofNat _ (heap address.toNat)) hn.heap
  · exact congrArg (BitVec.ofNat _) hn.old
  · exact congrArg (BitVec.ofNat _) hn.fresh
  · exact congrArg (BitVec.ofNat _) hn.value
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (workspaceBase_fits full.length q)]
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend]
  · exact hn.active

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBaseWord
