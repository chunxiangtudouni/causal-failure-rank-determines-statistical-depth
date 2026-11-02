module

public import PaperProofs.Structure.RawCandidateOrderingRAM
public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
import Mathlib.Tactic.IntervalCases

/-! Prefix bounds for the existing ordering array-address code.  Source
word Fits is required only for an actual load; no rank or sorted answer
is supplied.  The caller proves the separate logical index<M condition. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateOrderingArrayWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM
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

theorem arrayBase_effect (q : Nat) (full : List (Finset (Fin q))) (factor : Nat) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q) :
    (runOps (rawIncidenceROM q full) (arrayBase factor) state).register .address =
        workspaceBase full.length q + candidateCount full.length q * factor + 4 ∧
      (runOps (rawIncidenceROM q full) (arrayBase factor) state).heap = state.heap := by
  simp [arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hptr, hheader]

theorem arrayAddress_effect (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q) :
    (runOps (rawIncidenceROM q full) (arrayAddress factor counter) state).register .address =
        arraySlot (workspaceBase full.length q) (candidateCount full.length q) factor
          (state.heap (workspaceBase full.length q + counter)) ∧
      (runOps (rawIncidenceROM q full) (arrayAddress factor counter) state).heap = state.heap := by
  simp [arrayAddress, arrayBase, arraySlot, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
    Op.execute, Instruction.execute, hptr, hheader]

theorem arrayBase_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor : Nat) (hfactor : factor ≤ 4)
    (state : NatState) (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (count : Nat) (hc : count ≤ 12) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((arrayBase factor).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 12 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 12; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((arrayBase factor)[count]'(by change count < 12; exact hlt)) _)
    interval_cases count <;>
      simp only [arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)

theorem arrayBase_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor : Nat)
    (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 12) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((arrayBase factor).take count) state)
      ((arrayBase factor).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, h8, hB]

theorem arrayAddress_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (count : Nat) (hc : count ≤ 18) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((arrayAddress factor counter).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 18 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 18; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((arrayAddress factor counter)[count]'(by change count < 18; exact hlt)) _)
    interval_cases count <;>
      simp only [arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)

theorem arrayAddress_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hcounter : counter ≤ 3) (state : NatState) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count < 18) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((arrayAddress factor counter).take count) state)
      ((arrayAddress factor counter).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + counter < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, h8, hB, haddr]

theorem loadArray_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) factor
        (state.heap (workspaceBase full.length q + counter)))))
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target factor counter).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 19 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((loadArray target factor counter)[count]'(by change count < 19; exact hlt)) _)
    interval_cases count <;>
      simp only [loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, arraySlot])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold workspaceLimit
    all_goals nlinarith

theorem storeArray_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((storeArray factor counter).take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 19 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((storeArray factor counter)[count]'(by change count < 19; exact hlt)) _)
    interval_cases count <;>
      simp only [storeArray, arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; nlinarith)

theorem loadArray_prefix_access (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (count : Nat) (hc : count < 19) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target factor counter).take count) state)
      ((loadArray target factor counter).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + counter < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hm := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  interval_cases count <;>
    simp [loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hheader, h8, hB, haddr]
  all_goals unfold workspaceLimit
  all_goals nlinarith

theorem storeArray_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (count : Nat) (hc : count < 19) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((storeArray factor counter).take count) state)
      ((storeArray factor counter).getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have h8 : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hB : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + counter < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hm := Nat.mul_le_mul_left (candidateCount full.length q) hfactor
  interval_cases count <;>
    simp [storeArray, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hheader, h8, hB, haddr]
  all_goals unfold workspaceLimit
  all_goals nlinarith

end PaperProofs.Structure.LaminarTree.RawCandidateOrderingArrayWord
