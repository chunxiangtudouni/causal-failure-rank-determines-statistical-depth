module

public import PaperProofs.Structure.RawCandidateParentRAM
public import PaperProofs.Structure.RawCandidateOrderingArrayWord
import Mathlib.Tactic.IntervalCases

/-! Numerical and physical-access bounds for the original parent-address,
outer test and best-card initialization.  Only ordinary source-cell bounds
are hypotheses; no parent choice or future safe execution is supplied. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentWordAddress

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM
open RawCandidateOrderingRAM (arrayBase arrayAddress arraySlot loadWorkspace storeWorkspace)
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits)
open RawIncidenceScanSafety (NatAccessFits)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hr : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr reg

theorem parentAddress_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (count : Nat) (hc : count ≤ 20) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((parentAddress).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 20 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 20; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((parentAddress)[count]'(by change count < 20; exact hlt)) _)
    interval_cases count <;>
      simp only [parentAddress, arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp,
        natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [parentAddress, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold workspaceLimit
    all_goals nlinarith

theorem outerTest_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hcount : state.heap (nodeCountAddress (workspaceBase full.length q) (candidateCount full.length q)) ≤ candidateCount full.length q)
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit))
    (count : Nat) (hc : count ≤ 21) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((outerTest exit).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 21 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 21; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((outerTest exit)[count]'(by change count < 21; exact hlt)) _)
    interval_cases count <;>
      simp only [outerTest, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp,
        natArithmetic, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | exact hexit
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [outerTest, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, nodeCountAddress, arraySlot])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold workspaceLimit
    all_goals have hsub := Nat.sub_le (state.heap (workspaceBase full.length q + candidateCount full.length q * 4 + 4)) (state.heap (workspaceBase full.length q + 1))
    all_goals nlinarith

theorem initializeBestCard_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count ≤ 9) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((initializeBestCard).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hqM : q + 1 ≤ candidateCount full.length q := by unfold candidateCount; omega
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 9 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 9; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((initializeBestCard)[count]'(by change count < 9; exact hlt)) _)
    interval_cases count <;>
      simp only [initializeBestCard, storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp,
        Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [initializeBestCard, storeWorkspace, loadCell, runOps, natExecuteOp,
          Op.execute, Instruction.execute, raw_header_q])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold workspaceLimit
    all_goals nlinarith

theorem parentAddress_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 20) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((parentAddress).take count) state)
      ((parentAddress).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + 1 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [parentAddress, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hB, haddr]

theorem outerTest_prefix_access (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (count : Nat) (hc : count < 21) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((outerTest exit).take count) state)
      ((outerTest exit).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + 1 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [outerTest, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hB, haddr, hheader]
  all_goals unfold workspaceLimit
  all_goals omega

theorem initializeBestCard_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 9) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((initializeBestCard).take count) state)
      ((initializeBestCard).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [initializeBestCard, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8]
  all_goals first | (rw [raw_input_length]; omega) | (unfold workspaceLimit; omega)

end PaperProofs.Structure.LaminarTree.RawCandidateParentWordAddress
