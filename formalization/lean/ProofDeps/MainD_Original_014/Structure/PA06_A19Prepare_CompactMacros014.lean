module

public import Structure.PA06_A19Prepare_CompactWord008
public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

/-! PRIVATE UNCOMPILED small-base scalar macro instance.
The exact original ISA macros are reused, at implementation wordFactor32.
Base16 comes from006; count/counter/value facts below are internal boundary
obligations to discharge from actual loop data, not original A19 qualifications.
The linear limit is008's16+8M+8192. Common original F8192 allocation room is
handled byRoot's CommonRoom012; no independent larger factor is selected here. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactMacros014

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateRetentionRAM

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases he : reg = target
  · simpa only [he, Function.update_self] using hv
  · simpa only [Function.update_of_ne he] using hf reg

theorem small_constant_fits (N q value : Nat) (hv : value ≤ 16) :
    Fits (indexWidth 32 N q) value :=
  PA06A19PrepareCompactWord008.fits_width32_of_width16 N q value
    (RawCandidateWorkspaceWordMacros.small_constant_fits N q value hv)

theorem workspace_offset_lt_limit (N q offset : Nat) (hoffset : offset ≤ 3) :
    16 + offset < linearLimit N q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega

theorem workspace_offset_fits (N q offset : Nat) (hoffset : offset ≤ 3) :
    Fits (indexWidth 32 N q) (16 + offset) :=
  (workspace_offset_lt_limit N q offset hoffset).trans
    (PA06A19PrepareCompactWord008.fits_width32_of_width16 N q _
      (PA06A19PrepareCompactWord008.linearLimit_fits N q))

theorem load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hread : Fits (indexWidth 32 full.length q) (state.heap (16 + offset)))
    (count : Nat) (hc : count ≤ 5) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state) :=
  PA06A19PrepareCompactWord008.load_prefix_fit q full 16 offset target state hr hptr
    (small_constant_fits _ _ 8 (by decide)) (small_constant_fits _ _ 16 le_rfl)
    (small_constant_fits _ _ offset (by omega)) (workspace_offset_fits _ _ offset hoffset) hread count hc

theorem load_prefix_access (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state)
      ((loadWorkspace target offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  apply PA06A19PrepareCompactWord008.load_prefix_access q full 16 offset _ target state hptr
    (by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega)
    (workspace_offset_lt_limit _ _ offset hoffset) count hc

/-- Uses008's genuine store macro after the one real constant instruction. -/
theorem set_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hvalue : Fits (indexWidth 32 full.length q) value) (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((setWorkspace offset value).take count) state) := by
  cases count with
  | zero => exact hr
  | succ count =>
    let seeded := natExecuteOp (rawIncidenceROM q full) (.base (.base (.constant .total value))) state
    have hs : RegistersFit (indexWidth 32 full.length q) seeded := by
      exact fits_update hr .total value hvalue
    have hp : seeded.heap 8 = 16 := hptr
    change RegistersFit _ (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) seeded)
    exact PA06A19PrepareCompactWord008.store_prefix_fit q full 16 offset seeded hs hp
      (small_constant_fits _ _ 8 (by decide)) (small_constant_fits _ _ 16 le_rfl)
      (small_constant_fits _ _ offset (by omega)) (workspace_offset_fits _ _ offset hoffset)
      count (by omega)

theorem set_prefix_access (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 6) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((setWorkspace offset value).take count) state)
      ((setWorkspace offset value).getD count RawCandidateRetentionRAM.paddingOp) := by
  cases count with
  | zero => trivial
  | succ count =>
    let seeded := natExecuteOp (rawIncidenceROM q full) (.base (.base (.constant .total value))) state
    change NatAccessFits _ _ (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) seeded)
      ((storeWorkspace offset).getD count RawCandidateRetentionRAM.paddingOp)
    have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
    exact PA06A19PrepareCompactWord008.store_prefix_access q full 16 offset _ seeded hptr h8
      (workspace_offset_lt_limit _ _ offset hoffset) count (by omega)

theorem increment_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hinc : Fits (indexWidth 32 full.length q) (state.heap (16 + offset) + 1))
    (count : Nat) (hc : count ≤ 12) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace offset).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hone := small_constant_fits full.length q 1 (by decide)
  have hB := small_constant_fits full.length q 16 (by decide)
  have hoff := small_constant_fits full.length q offset (by omega)
  have hadd := workspace_offset_fits full.length q offset hoffset
  have hread : Fits (indexWidth 32 full.length q) (state.heap (16 + offset)) :=
    (Nat.le_succ _).trans_lt hinc
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 12 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 12; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((incrementWorkspace offset)[count]'(by change count < 12; exact hlt)) _)
    interval_cases count <;>
      simp only [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact h8
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hadd
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hread
    · exact hone
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hinc
    · exact h8
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp,
        Op.execute, Instruction.execute, hptr] using hadd

theorem increment_prefix_access (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 12) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace offset).take count) state)
      ((incrementWorkspace offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by
    unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    omega
  have hb := workspace_offset_lt_limit full.length q offset hoffset
  interval_cases count <;>
    simp [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb]

theorem test_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (counter exit : Nat)
    (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hcount : Fits (indexWidth 32 full.length q) (state.heap (16)))
    (hcounter : Fits (indexWidth 32 full.length q) (state.heap (16 + counter)))
    (hexit : Fits (indexWidth 32 full.length q) (5 * exit))
    (count : Nat) (hc : count ≤ 13) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((testWorkspace counter exit).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hzero := small_constant_fits full.length q 0 (by decide)
  have hB := small_constant_fits full.length q 16 (by decide)
  have hoff := small_constant_fits full.length q counter (by omega)
  have hadd := workspace_offset_fits full.length q counter hoffset
  have hsub : Fits (indexWidth 32 full.length q)
      (state.heap (16) - state.heap (16 + counter)) :=
    (Nat.sub_le _ _).trans_lt hcount
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 13 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 13; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((testWorkspace counter exit)[count]'(by change count < 13; exact hlt)) _)
    interval_cases count <;>
      simp only [testWorkspace, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact h8
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · exact hzero
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hcount
    · exact h8
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hadd
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hcounter
    · simpa [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hsub
    · exact hexit

theorem test_prefix_access (q : Nat) (full : List (Finset (Fin q))) (counter exit : Nat)
    (hoffset : counter ≤ 3) (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 13) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((testWorkspace counter exit).take count) state)
      ((testWorkspace counter exit).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by
    unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    omega
  have hb := workspace_offset_lt_limit full.length q counter hoffset
  have hbase : 16 < linearLimit full.length q := by
    simpa only [Nat.add_zero] using workspace_offset_lt_limit full.length q 0 (by decide)
  interval_cases count <;>
    simp [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb, hbase]

/-- Encoded execution includes the real last conditional jump; a noJump
claim about the whole test macro is deliberately not used. -/
theorem test_run_segment (rom : PhysicalROM) (containing : List PackingOp)
    (start counter exit : Nat) (hbound : start + 13 ≤ containing.length)
    (hcode : ∀ position < 13, containing.getD (start + position) RawCandidateRetentionRAM.paddingOp =
      (testWorkspace counter exit).getD position RawCandidateRetentionRAM.paddingOp)
    (state : NatState) (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    natRun rom containing 13 state = runOps rom (testWorkspace counter exit) state := by
  let lead := (testWorkspace counter exit).take 12
  have hlen : lead.length = 12 := by rfl
  have hsplit : testWorkspace counter exit = lead ++ [.jumpIfZero .flag .index] := by rfl
  have hlead : ∀ op ∈ lead, NoJump op := by
    simp [lead, testWorkspace, loadWorkspace, loadCell, NoJump]
  have hfull : runOps rom (testWorkspace counter exit) state =
      natExecuteOp rom (.jumpIfZero .flag .index) (runOps rom lead state) := by
    rw [hsplit, runOps_append]
    rfl
  have hr := natRun_of_segment_last rom containing lead (.jumpIfZero .flag .index) start
    (by rw [hlen]; exact hbound) (by
      intro position hp
      have hh := hcode position (by rw [hlen] at hp; omega)
      rw [List.getD_eq_getElem _ _ (by omega),
        List.getD_eq_getElem _ _ (by change position < 13; rw [hlen] at hp; omega)] at hh
      simpa only [lead, List.getElem_take] using hh) (by
      have hh := hcode 12 (by decide)
      rw [List.getD_eq_getElem _ _ (by omega)] at hh
      simpa [hlen, testWorkspace, loadWorkspace, loadCell] using hh) hlead state hpc ha
  rw [hlen] at hr
  exact hr.trans hfull.symm

theorem test_run_values (rom : PhysicalROM) (containing : List PackingOp)
    (start counter exit : Nat) (hbound : start + 13 ≤ containing.length)
    (hcode : ∀ position < 13, containing.getD (start + position) RawCandidateRetentionRAM.paddingOp =
      (testWorkspace counter exit).getD position RawCandidateRetentionRAM.paddingOp)
    (state : NatState) (hptr : state.heap 8 = 16)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let result := natRun rom containing 13 state
    result.heap = state.heap ∧
      result.pc = (if state.heap 16 - state.heap (16 + counter) = 0 then 5 * exit else 5 * (start + 13)) ∧
      result.halted = false := by
  rw [test_run_segment rom containing start counter exit hbound hcode state hpc ha]
  have hp : 5 * start + 65 = 5 * (start + 13) := by omega
  simpa only [hptr, hpc, ha, hp] using (testWorkspace_values rom counter exit state)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactMacros014
