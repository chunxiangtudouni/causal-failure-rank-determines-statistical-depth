module

public import PaperProofs.Structure.RawCandidateRetentionRAM
public import PaperProofs.Structure.RawCandidateWorkspaceBounds
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.RawIncidenceOuterSafety
import Mathlib.Tactic.IntervalCases

/-! Prefix word and access bounds for the existing candidate workspace
macros.  Source-cell word bounds are ordinary caller invariants; no computed
card, keep, rank, or safe execution is assumed as an answer.  Linking these
instruction-list prefixes to actual control flow remains a separate step. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceWordMacros

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateWorkspaceInit RawCandidateWorkspaceBounds
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateRetentionRAM (loadWorkspace storeWorkspace setWorkspace incrementWorkspace testWorkspace)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hr : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr reg

theorem small_constant_fits (N q value : Nat) (hv : value ≤ 16) : Fits (indexWidth 16 N q) value :=
  (hv.trans (workspaceBase_ge N q)).trans_lt (workspaceBase_fits N q)

theorem workspace_offset_lt_limit (N q offset : Nat) (hoffset : offset ≤ 3) :
    workspaceBase N q + offset < workspaceLimit N q := by
  unfold workspaceLimit
  omega

theorem workspace_offset_fits (N q offset : Nat) (hoffset : offset ≤ 3) :
    Fits (indexWidth 16 N q) (workspaceBase N q + offset) :=
  (workspace_offset_lt_limit N q offset hoffset).trans (workspaceLimit_fits N q)

theorem load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hread : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset)))
    (count : Nat) (hc : count ≤ 5) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hB := workspaceBase_fits full.length q
  have hoff := small_constant_fits full.length q offset (by omega)
  have hadd := workspace_offset_fits full.length q offset hoffset
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 5 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 5; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((loadWorkspace target offset)[count]'(by change count < 5; exact hlt)) _)
    interval_cases count <;>
      simp only [loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    · exact h8
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hadd
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hread

theorem load_prefix_access (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state)
      ((loadWorkspace target offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < workspaceLimit full.length q := by
    unfold workspaceLimit
    have h := workspaceBase_ge full.length q
    omega
  have hb := workspace_offset_lt_limit full.length q offset hoffset
  interval_cases count <;>
    simp [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb]

theorem store_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count ≤ 5) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hB := workspaceBase_fits full.length q
  have hoff := small_constant_fits full.length q offset (by omega)
  have hadd := workspace_offset_fits full.length q offset hoffset
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 5 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 5; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((storeWorkspace offset)[count]'(by change count < 5; exact hlt)) _)
    interval_cases count <;>
      simp only [storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact h8
    · simpa [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hadd

theorem store_prefix_access (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) state)
      ((storeWorkspace offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < workspaceLimit full.length q := by
    unfold workspaceLimit
    have h := workspaceBase_ge full.length q
    omega
  have hb := workspace_offset_lt_limit full.length q offset hoffset
  interval_cases count <;>
    simp [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb]

theorem set_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hvalue : Fits (indexWidth 16 full.length q) value)
    (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((setWorkspace offset value).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hB := workspaceBase_fits full.length q
  have hoff := small_constant_fits full.length q offset (by omega)
  have hadd := workspace_offset_fits full.length q offset hoffset
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 6 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 6; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((setWorkspace offset value)[count]'(by change count < 6; exact hlt)) _)
    interval_cases count <;>
      simp only [setWorkspace, storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact hvalue
    · exact h8
    · simpa [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hB
    · exact hoff
    · simpa [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hadd

theorem set_prefix_access (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 6) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((setWorkspace offset value).take count) state)
      ((setWorkspace offset value).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < workspaceLimit full.length q := by
    unfold workspaceLimit
    have h := workspaceBase_ge full.length q
    omega
  have hb := workspace_offset_lt_limit full.length q offset hoffset
  interval_cases count <;>
    simp [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb]

theorem increment_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset) + 1))
    (count : Nat) (hc : count ≤ 12) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace offset).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hone := small_constant_fits full.length q 1 (by decide)
  have hB := workspaceBase_fits full.length q
  have hoff := small_constant_fits full.length q offset (by omega)
  have hadd := workspace_offset_fits full.length q offset hoffset
  have hread : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset)) :=
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
    (hoffset : offset ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 12) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace offset).take count) state)
      ((incrementWorkspace offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < workspaceLimit full.length q := by
    unfold workspaceLimit
    have h := workspaceBase_ge full.length q
    omega
  have hb := workspace_offset_lt_limit full.length q offset hoffset
  interval_cases count <;>
    simp [incrementWorkspace, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb]

theorem test_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (counter exit : Nat)
    (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hcount : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q)))
    (hcounter : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + counter)))
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit))
    (count : Nat) (hc : count ≤ 13) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((testWorkspace counter exit).take count) state) := by
  have h8 := small_constant_fits full.length q 8 (by decide)
  have hzero := small_constant_fits full.length q 0 (by decide)
  have hB := workspaceBase_fits full.length q
  have hoff := small_constant_fits full.length q counter (by omega)
  have hadd := workspace_offset_fits full.length q counter hoffset
  have hsub : Fits (indexWidth 16 full.length q)
      (state.heap (workspaceBase full.length q) - state.heap (workspaceBase full.length q + counter)) :=
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
    (hoffset : counter ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 13) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((testWorkspace counter exit).take count) state)
      ((testWorkspace counter exit).getD count RawCandidateRetentionRAM.paddingOp) := by
  have h8 : 8 < workspaceLimit full.length q := by
    unfold workspaceLimit
    have h := workspaceBase_ge full.length q
    omega
  have hb := workspace_offset_lt_limit full.length q counter hoffset
  have hbase : workspaceBase full.length q < workspaceLimit full.length q := by
    simpa only [Nat.add_zero] using workspace_offset_lt_limit full.length q 0 (by decide)
  interval_cases count <;>
    simp [testWorkspace, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hb, hbase]

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceWordMacros
