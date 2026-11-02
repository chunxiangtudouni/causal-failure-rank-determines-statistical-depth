module

public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
public import PaperProofs.Structure.RawCandidateOrderingArrayWord
public import PaperProofs.Structure.RawCandidatePairScanWord
public import PaperProofs.Structure.CompactControllerClaims
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

/-! PRIVATE UNCOMPILED minimal compact-word foundation.
Only two existing real5-op workspace macros are generalized over base/heap.
No retention/order/parent whole-loop safety is inferred from these helpers.
The old large workspace bound is used only to bound logarithmic WORD VALUES,
never as an allocation or a granted old heap address. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactWord008

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateRetentionRAM

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases he : reg = target
  · simpa only [he, Function.update_self] using hv
  · simpa only [Function.update_of_ne he] using hf reg

theorem compactEnd_fits (N q : Nat) :
    Fits (indexWidth 16 N q) (16 + 5 + 5 * (N + q + 1)) := by
  apply lt_of_le_of_lt _ (RawCandidateWorkspaceBounds.workspaceLimit_fits N q)
  have hb := RawCandidateWorkspaceInit.workspaceBase_ge N q
  unfold RawCandidateWorkspaceBounds.workspaceLimit RawCandidateWorkspaceInit.candidateCount
  omega

/-- Conservative LINEAR limit for private instantiation of old proof
pieces. It is a proof allocation choice, not a matrix or old high B. -/
def linearLimit (N q : Nat) : Nat := 16 + 8 * (N + q + 1) + 8192

theorem linearLimit_le_mul (N q : Nat) : linearLimit N q ≤ 8224 * (N + q + 1) := by
  unfold linearLimit
  omega

theorem linearLimit_fits (N q : Nat) : Fits (indexWidth 16 N q) (linearLimit N q) := by
  apply lt_of_le_of_lt _ (RawCandidateWorkspaceBounds.workspaceLimit_fits N q)
  have hb := RawCandidateWorkspaceInit.workspaceBase_ge N q
  unfold linearLimit RawCandidateWorkspaceBounds.workspaceLimit RawCandidateWorkspaceInit.candidateCount
  omega

theorem linearLimit_room (N q t packed indexFactor : Nat) (hi : 16384 ≤ indexFactor) :
    linearLimit N q ≤ 4 + packed + indexFactor * (N + q + t + 1) := by
  have hm := Nat.mul_le_mul_right (N + q + t + 1) hi
  have hl := linearLimit_le_mul N q
  omega

/-- Same ORIGINAL compact heap expression; no old large workspace allocation. -/
theorem compactEnd_room (N q t packed indexFactor : Nat) (hi : 64 ≤ indexFactor) :
    16 + 5 + 5 * (N + q + 1) ≤ 4 + packed + indexFactor * (N + q + t + 1) := by
  have hm := Nat.mul_le_mul_right (N + q + t + 1) hi
  omega

theorem fits_width32_of_width16 (N q value : Nat) (hv : Fits (indexWidth 16 N q) value) :
    Fits (indexWidth 32 N q) value := by
  have hw : indexWidth 16 N q ≤ indexWidth 32 N q := by
    unfold indexWidth
    omega
  exact hv.trans_le (Nat.pow_le_pow_right (by decide) hw)

/-- Genuine existing loadWorkspace5-op, now on actual base16 or any proved
base. Value/offset/address Fits are local facts to discharge from real data. -/
theorem load_prefix_fit {bits : Nat} (q : Nat) (full : List (Finset (Fin q)))
    (base offset : Nat) (target : Register) (state : NatState)
    (hf : RegistersFit bits state) (hptr : state.heap 8 = base)
    (h8 : Fits bits 8) (hbase : Fits bits base) (hoff : Fits bits offset)
    (haddress : Fits bits (base + offset)) (hread : Fits bits (state.heap (base + offset)))
    (count : Nat) (hc : count ≤ 5) :
    RegistersFit bits (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state) := by
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hlt : count < 5 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 5; exact hlt), runOps_append]
    change RegistersFit bits (natExecuteOp _ ((loadWorkspace target offset)[count]'(by change count < 5; exact hlt)) _)
    interval_cases count <;>
      simp only [loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    · exact h8
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hoff
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using haddress
    · simpa [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hread

theorem load_prefix_access (q : Nat) (full : List (Finset (Fin q)))
    (base offset heapWords : Nat) (target : Register) (state : NatState)
    (hptr : state.heap 8 = base) (h8 : 8 < heapWords) (haddress : base + offset < heapWords)
    (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) heapWords
      (runOps (rawIncidenceROM q full) ((loadWorkspace target offset).take count) state)
      ((loadWorkspace target offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  interval_cases count <;>
    simp [loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, haddress]

theorem store_prefix_fit {bits : Nat} (q : Nat) (full : List (Finset (Fin q)))
    (base offset : Nat) (state : NatState) (hf : RegistersFit bits state) (hptr : state.heap 8 = base)
    (h8 : Fits bits 8) (hbase : Fits bits base) (hoff : Fits bits offset)
    (haddress : Fits bits (base + offset)) (count : Nat) (hc : count ≤ 5) :
    RegistersFit bits (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) state) := by
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hlt : count < 5 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 5; exact hlt), runOps_append]
    change RegistersFit bits (natExecuteOp _ ((storeWorkspace offset)[count]'(by change count < 5; exact hlt)) _)
    interval_cases count <;>
      simp only [storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact h8
    · simpa [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hoff
    · simpa [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using haddress

theorem store_prefix_access (q : Nat) (full : List (Finset (Fin q)))
    (base offset heapWords : Nat) (state : NatState)
    (hptr : state.heap 8 = base) (h8 : 8 < heapWords) (haddress : base + offset < heapWords)
    (count : Nat) (hc : count < 5) :
    NatAccessFits (rawIncidenceROM q full) heapWords
      (runOps (rawIncidenceROM q full) ((storeWorkspace offset).take count) state)
      ((storeWorkspace offset).getD count RawCandidateRetentionRAM.paddingOp) := by
  interval_cases count <;>
    simp [storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, haddress]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactWord008
