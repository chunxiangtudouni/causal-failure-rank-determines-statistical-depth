module

public import Structure.PA06_A19Prepare_CompactOrdering034Macros
public import PaperProofs.Structure.RawCandidateParentWordAddress

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Real parent-address20, outer-test21 and best-card-init9 prefixes at
B16/full width32/008linearLimit. The original fixed ISA is unchanged;
source qualifications concern actual header/node/count cells. No parent
answer, hSafe or old width16 caller qualification is supplied. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Address

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM RawIncidenceScanSafety
open RawCandidateOrderingRAM (arrayBase arrayAddress arraySlot loadWorkspace storeWorkspace)
open PA06A19PrepareCompactOrdering034Macros (fits_update)

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

theorem parentAddress_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + 1) ≤ (full.length + q + 1))
    (count : Nat) (hc : count ≤ 20) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((parentAddress).take count) state) := by
  have hlimit : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
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
      
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [parentAddress, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    all_goals nlinarith

theorem outerTest_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + 1) ≤ (full.length + q + 1))
    (hcount : state.heap (nodeCountAddress 16 (full.length + q + 1)) ≤ (full.length + q + 1))
    (hexit : Fits (indexWidth 32 full.length q) (5 * exit))
    (count : Nat) (hc : count ≤ 21) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((outerTest exit).take count) state) := by
  have hlimit : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
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
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [outerTest, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
          Op.execute, Instruction.execute, nodeCountAddress, arraySlot])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    all_goals have hsub := Nat.sub_le (state.heap (16 + (full.length + q + 1) * 4 + 4)) (state.heap (16 + 1))
    all_goals nlinarith

theorem initializeBestCard_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count ≤ 9) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((initializeBestCard).take count) state) := by
  have hlimit : Fits (indexWidth 32 full.length q) (linearLimit full.length q) := PA06A19PrepareCompactArrays018.linearLimit_fits full.length q
  have hqM : q + 1 ≤ (full.length + q + 1) := by omega
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
      
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [initializeBestCard, storeWorkspace, loadCell, runOps, natExecuteOp,
          Op.execute, Instruction.execute, raw_header_q])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    all_goals nlinarith

theorem parentAddress_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 20) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((parentAddress).take count) state)
      ((parentAddress).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + 1 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [parentAddress, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hB, haddr]

theorem outerTest_prefix_access (q : Nat) (full : List (Finset (Fin q))) (exit : Nat) (state : NatState)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (count : Nat) (hc : count < 21) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((outerTest exit).take count) state)
      ((outerTest exit).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + 1 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [outerTest, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8, hB, haddr, hheader]
  all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
  all_goals omega

theorem initializeBestCard_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 9) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((initializeBestCard).take count) state)
      ((initializeBestCard).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [initializeBestCard, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, h8]
  all_goals first | (rw [raw_input_length]; omega) | (unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega)


end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Address

