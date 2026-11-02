module

public import PaperProofs.Structure.RawCandidateRetentionWordChunks

/-! The small retention pieces only require bounds on the cells they
actually read.  Their hypotheses do not supply card/keep answers, and are
to be discharged at the actual loop boundaries. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
  RawCandidateWorkspaceInit RawCandidateWorkspaceBounds
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkLength)

def Needs (q : Nat) (full : List (Finset (Fin q))) (chunk : Chunk) (state : NatState) : Prop :=
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  state.heap 8 = B ∧
    match chunk with
    | .initialize => True
    | .outerTest => state.heap B = M ∧ state.heap (B + 1) ≤ M
    | .cardArgs => state.heap (B + 1) ≤ M
    | .afterCard => state.heap 1 ≤ M ∧ state.heap 4 ≤ q
    | .innerTest => state.heap B = M ∧ state.heap (B + 2) ≤ M
    | .pairArgs => state.heap (B + 1) ≤ M ∧ state.heap (B + 2) ≤ M
    | .innerTail => state.heap 5 ≤ q ∧ state.heap 6 ≤ q ∧ state.heap (B + 3) ≤ 1 ∧ state.heap (B + 2) ≤ M
    | .finish => state.heap B = M ∧ state.heap 1 ≤ M ∧ state.heap (B + 1) ≤ M ∧ state.heap (B + 3) ≤ 1

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hr : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr reg

theorem cardArgs_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (count : Nat) (hc : count ≤ 10) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (cardArguments.take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hM := candidateCount_fits full.length q
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 10 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 10; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (cardArguments[count]'(by change count < 10; exact hlt)) _)
    interval_cases count <;>
      simp only [cardArguments, loadWorkspace, loadCell, storeCell, setCell, List.getElem_append,
        List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega)
      | (simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute];
          (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega))

theorem pairArgs_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hj : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (count : Nat) (hc : count ≤ 14) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (pairArguments.take count) state) := by
  have hB := workspaceBase_ge full.length q
  have hlimit := workspaceLimit_fits full.length q
  have hnB2 : workspaceBase full.length q + 2 ≠ 1 := by omega
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 14 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 14; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ (pairArguments[count]'(by change count < 14; exact hlt)) _)
    interval_cases count <;>
      simp only [pairArguments, loadWorkspace, loadCell, storeCell, List.getElem_append,
        List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega)
      | (simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute];
          (apply lt_of_le_of_lt _ hlimit; unfold workspaceLimit; omega))

theorem cardArgs_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 10) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (cardArguments.take count) state)
      (cardArguments.getD count RawCandidateRetentionRAM.paddingOp) := by
  have hB := workspaceBase_ge full.length q
  have hlim : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr : workspaceBase full.length q + 1 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [cardArguments, loadWorkspace, loadCell, storeCell, setCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hlim, haddr]
  all_goals omega

theorem pairArgs_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 14) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (pairArguments.take count) state)
      (pairArguments.getD count RawCandidateRetentionRAM.paddingOp) := by
  have hB := workspaceBase_ge full.length q
  have hlim : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr1 : workspaceBase full.length q + 1 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have haddr2 : workspaceBase full.length q + 2 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  interval_cases count <;>
    simp [pairArguments, loadWorkspace, loadCell, storeCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hlim, haddr1, haddr2]
  all_goals omega

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordBounds
