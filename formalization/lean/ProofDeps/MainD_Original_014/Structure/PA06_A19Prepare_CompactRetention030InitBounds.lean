module

public import Structure.PA06_A19Prepare_CompactInit006
public import Structure.PA06_A19Prepare_CompactMacros014
public import PaperProofs.Structure.RawIncidenceWorkspace

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! The short006 initializer at FULL width32. The real dispatcher writes
its final-code PC into index, so fitting all incoming registers in width16
would wrongly restrict arbitrary allowed later code. Only this16-op prefix
certificate is generalized;006's actual code and Nat correctness are reused.
The old polynomial bound below is solely a logarithmic WORD VALUE bound
for the already executed M*q register arithmetic, never an allocation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030InitBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareCompactInit006 (initProgram)
open RawCandidateWorkspaceInit (candidateCount)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases he : reg = target
  · simpa only [he, Function.update_self] using hv
  · simpa only [Function.update_of_ne he] using hf reg

theorem init_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) (count : Nat) (hc : count ≤ 16) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) (initProgram.take count) state) := by
  have hM := PA06A19PrepareCompactWord008.fits_width32_of_width16 full.length q _
    (RawCandidateWorkspaceInit.candidateCount_fits full.length q)
  have hdim (value : Nat) (hv : value ≤ candidateCount full.length q) : Fits (indexWidth 32 full.length q) value :=
    hv.trans_lt hM
  have hN : Fits (indexWidth 32 full.length q) full.length := hdim _ (by unfold candidateCount; omega)
  have hq : Fits (indexWidth 32 full.length q) q := hdim _ (by unfold candidateCount; omega)
  have hsum : Fits (indexWidth 32 full.length q) (full.length + q) := hdim _ (by unfold candidateCount; omega)
  have hMQ : Fits (indexWidth 32 full.length q) ((full.length + q + 1) * q) := by
    apply PA06A19PrepareCompactWord008.fits_width32_of_width16
    apply lt_of_le_of_lt _ (RawCandidateWorkspaceInit.workspaceBase_fits full.length q)
    unfold RawCandidateWorkspaceInit.workspaceBase candidateCount
    nlinarith
  have hconstant (value : Nat) (hv : value ≤ 16) : Fits (indexWidth 32 full.length q) value :=
    PA06A19PrepareCompactMacros014.small_constant_fits full.length q value hv
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


/-- An active checker prefix lies before its already proved finite halt.
This obtains the actual checker certificate; it is not a caller hSafe. -/
theorem checker_active_point (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (active : (natRun (rawIncidenceROM q full) checker count natInitial).halted = false) :
    RawIncidenceScanSafety.SafePoint q full (natRun (rawIncidenceROM q full) checker count natInitial) := by
  obtain ⟨steps, _bound, safe, halted⟩ := checker_has_safe_halt q full
  have within : count ≤ steps := by
    by_contra outside
    have same : natRun (rawIncidenceROM q full) checker count natInitial =
        natRun (rawIncidenceROM q full) checker steps natInitial := by
      conv_lhs => rw [show count = steps + (count - steps) by omega]
      exact natRun_after_halt (rawIncidenceROM q full) checker natInitial steps halted (count - steps)
    rw [same, halted] at active
    cases active
  exact safe count within

theorem checker_active_registersFit (q : Nat) (full : List (Finset (Fin q))) (count : Nat)
    (active : (natRun (rawIncidenceROM q full) checker count natInitial).halted = false) :
    RegistersFit (indexWidth 32 full.length q) (natRun (rawIncidenceROM q full) checker count natInitial) := by
  have original := safePoint_registersFit q full _ (checker_active_point q full count active)
  intro reg
  exact PA06A19PrepareCompactWord008.fits_width32_of_width16 full.length q _ (original reg)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention030InitBounds

