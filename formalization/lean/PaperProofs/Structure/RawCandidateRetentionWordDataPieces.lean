module

public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
public import PaperProofs.Structure.RawCandidateRetentionWordChunks
import Mathlib.Tactic.IntervalCases

/-! Prefix numerical and access bounds for the three existing retention
data pieces. Their hypotheses bound ordinary source cells; no computed
card/keep answer or safe execution is supplied. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordDataPieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge workspaceBase_fits candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateRetentionRAM

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

private theorem scalar_fits (N q value : Nat) (hv : value ≤ 2 * candidateCount N q + 16) :
    Fits (indexWidth 16 N q) value := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

private theorem prefix_fit_append (rom : PhysicalROM) (bits : Nat) (first second : List PackingOp) (state : NatState)
    (hfirst : ∀ count ≤ first.length, RegistersFit bits (runOps rom (first.take count) state))
    (hsecond : ∀ count ≤ second.length, RegistersFit bits (runOps rom (second.take count) (runOps rom first state)))
    (count : Nat) (hc : count ≤ (first ++ second).length) :
    RegistersFit bits (runOps rom ((first ++ second).take count) state) := by
  by_cases hsmall : count ≤ first.length
  · rw [List.take_append_of_le_length hsmall]
    exact hfirst count hsmall
  · rw [List.take_append, List.take_of_length_le (by omega), runOps_append]
    apply hsecond
    simp only [List.length_append] at hc
    omega

private theorem prefix_access_append (rom : PhysicalROM) (heapWords : Nat) (first second : List PackingOp) (state : NatState)
    (hfirst : ∀ count < first.length,
      NatAccessFits rom heapWords (runOps rom (first.take count) state) (first.getD count paddingOp))
    (hsecond : ∀ count < second.length,
      NatAccessFits rom heapWords (runOps rom (second.take count) (runOps rom first state)) (second.getD count paddingOp))
    (count : Nat) (hc : count < (first ++ second).length) :
    NatAccessFits rom heapWords (runOps rom ((first ++ second).take count) state) ((first ++ second).getD count paddingOp) := by
  by_cases hsmall : count < first.length
  · rw [List.take_append_of_le_length hsmall.le, List.getD_append _ _ _ _ hsmall]
    exact hfirst count hsmall
  · rw [List.take_append, List.take_of_length_le (by omega), runOps_append,
      List.getD_append_right _ _ _ _ (by omega)]
    apply hsecond
    simp only [List.length_append] at hc
    omega

theorem storeCard_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (h4 : state.heap 4 ≤ q)
    (count : Nat) (hc : count ≤ 10) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (storeCard.take count) state) := by
  have hb := workspaceBase_ge full.length q
  have hd : q ≤ candidateCount full.length q := by unfold candidateCount; omega
  have hread := scalar_fits full.length q (state.heap 4) (by omega)
  have hindex := scalar_fits full.length q (state.heap 1) (by omega)
  have hbase := workspaceBase_fits full.length q
  have hplus4 : Fits (indexWidth 16 full.length q) (workspaceBase full.length q + 4) := by
    apply workspace_address_fits
    unfold workspaceLimit
    omega
  have hadd : Fits (indexWidth 16 full.length q) (workspaceBase full.length q + 4 + state.heap 1) := by
    apply workspace_address_fits
    unfold workspaceLimit
    omega
  have hsmall (value : Nat) (hv : value ≤ 16) := RawCandidateWorkspaceWordMacros.small_constant_fits full.length q value hv
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 10 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 10; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (storeCard[count]'(by change count < 10; exact hc')) _)
    interval_cases count <;>
      simp only [storeCard, loadCell, List.getElem_append, List.getElem_cons_zero, List.getElem_cons_succ,
        List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact hsmall 4 (by decide)
    · simpa [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hread
    · exact hsmall 1 (by decide)
    · simpa [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hindex
    · exact hsmall 8 (by decide)
    · simpa [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 4 (by decide)
    · simpa [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hplus4
    · simpa [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hadd

theorem storeCard_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (h1 : state.heap 1 ≤ candidateCount full.length q)
    (count : Nat) (hc : count < 10) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (storeCard.take count) state) (storeCard.getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have hsmall : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hadd : workspaceBase full.length q + 4 + state.heap 1 < workspaceLimit full.length q := by
    unfold workspaceLimit
    omega
  interval_cases count <;>
    simp [storeCard, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, hsmall, hadd]
  all_goals omega

theorem updateFlag_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (h5 : state.heap 5 ≤ q) (h6 : state.heap 6 ≤ q) (hflag : state.heap (workspaceBase full.length q + 3) ≤ 1)
    (count : Nat) (hc : count ≤ 17) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (updateFlag.take count) state) := by
  have hd : q ≤ candidateCount full.length q := by unfold candidateCount; omega
  have hread5 := scalar_fits full.length q (state.heap 5) (by omega)
  have hread6 := scalar_fits full.length q (state.heap 6) (by omega)
  have hsum := scalar_fits full.length q (state.heap 5 + state.heap 6) (by omega)
  have hread := scalar_fits full.length q (state.heap (workspaceBase full.length q + 3)) (by omega)
  have hselect : Fits (indexWidth 16 full.length q)
      (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap (workspaceBase full.length q + 3)) := by
    split <;> apply scalar_fits <;> omega
  have hbase := workspaceBase_fits full.length q
  have hplus3 := RawCandidateWorkspaceWordMacros.workspace_offset_fits full.length q 3 le_rfl
  have hsmall (value : Nat) (hv : value ≤ 16) := RawCandidateWorkspaceWordMacros.small_constant_fits full.length q value hv
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 17 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 17; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (updateFlag[count]'(by change count < 17; exact hc')) _)
    interval_cases count <;>
      simp only [updateFlag, loadWorkspace, storeWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact hsmall 5 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hread5
    · exact hsmall 6 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hread6
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hsum
    · exact hsmall 8 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 3 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hplus3
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hread
    · exact hsmall 0 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hselect
    · exact hsmall 8 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 3 (by decide)
    · simpa [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hplus3

theorem updateFlag_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 17) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (updateFlag.take count) state) (updateFlag.getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have hsmall : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hplus3 := RawCandidateWorkspaceWordMacros.workspace_offset_lt_limit full.length q 3 le_rfl
  interval_cases count <;>
    simp [updateFlag, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, hsmall, hplus3]
  all_goals omega

theorem storeKeep_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (hM : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (hflag : state.heap (workspaceBase full.length q + 3) ≤ 1)
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (storeKeep.take count) state) := by
  have hread := scalar_fits full.length q (state.heap (workspaceBase full.length q + 3)) (by omega)
  have hindex := scalar_fits full.length q (state.heap 1) (by omega)
  have hbase := workspaceBase_fits full.length q
  have hplus3 := RawCandidateWorkspaceWordMacros.workspace_offset_fits full.length q 3 le_rfl
  have hplus4 : Fits (indexWidth 16 full.length q) (workspaceBase full.length q + 4) := by
    apply workspace_address_fits
    unfold workspaceLimit
    omega
  have hplusM : Fits (indexWidth 16 full.length q) (workspaceBase full.length q + 4 + candidateCount full.length q) := by
    apply workspace_address_fits
    unfold workspaceLimit
    omega
  have hadd : Fits (indexWidth 16 full.length q) (workspaceBase full.length q + 4 + candidateCount full.length q + state.heap 1) := by
    apply workspace_address_fits
    unfold workspaceLimit
    omega
  have hcount := candidateCount_fits full.length q
  have hsmall (value : Nat) (hv : value ≤ 16) := RawCandidateWorkspaceWordMacros.small_constant_fits full.length q value hv
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 19 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (storeKeep[count]'(by change count < 19; exact hc')) _)
    interval_cases count <;>
      simp only [storeKeep, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero, List.getElem_cons_succ,
        List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    · exact hsmall 8 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 3 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hplus3
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hread
    · exact hsmall 1 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hindex
    · exact hsmall 8 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 0 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr, hM] using hcount
    · exact hsmall 8 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hbase
    · exact hsmall 4 (by decide)
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr] using hplus4
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr, hM] using hplusM
    · simpa [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr, hM] using hadd

theorem storeKeep_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hM : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (count : Nat) (hc : count < 19) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (storeKeep.take count) state) (storeKeep.getD count paddingOp) := by
  have hb := workspaceBase_ge full.length q
  have hsmall : 8 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hplus3 := RawCandidateWorkspaceWordMacros.workspace_offset_lt_limit full.length q 3 le_rfl
  have hbase : workspaceBase full.length q < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hadd : workspaceBase full.length q + 4 + candidateCount full.length q + state.heap 1 < workspaceLimit full.length q := by
    unfold workspaceLimit
    omega
  interval_cases count <;>
    simp [storeKeep, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
      NatAccessFits, AccessFits, hptr, hM, hsmall, hplus3, hbase, hadd]
  all_goals omega

private theorem full_fit_of_prefix (rom : PhysicalROM) (bits : Nat) (code : List PackingOp) (state : NatState)
    (h : ∀ count ≤ code.length, RegistersFit bits (runOps rom (code.take count) state)) :
    RegistersFit bits (runOps rom code state) := by
  have hf := h code.length le_rfl
  simpa only [List.take_length] using hf

theorem setInitialFlag_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (count : Nat) (hc : count ≤ 7) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (setInitialFlag.take count) state) := by
  let core : List PackingOp := [.base (.base (.constant .old 1)), .base (.base (.minimum .total .old .total))]
  have hmin : min 1 (state.register .total) ≤ 1 := Nat.min_le_left _ _
  have cp : ∀ count ≤ core.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (core.take count) state) := by
    intro count hc
    change count ≤ 2 at hc
    interval_cases count <;> intro reg <;> cases reg <;>
      simp [core, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hf _ | apply scalar_fits; omega
  have cf := full_fit_of_prefix _ _ core state cp
  have ch : (runOps (rawIncidenceROM q full) core state).heap = state.heap := rfl
  exact prefix_fit_append _ _ core (storeWorkspace 3) state cp (by
    intro count hc
    exact RawCandidateWorkspaceWordMacros.store_prefix_fit q full 3 le_rfl _ cf
      ((congrFun ch 8).trans hptr) count hc) count hc

theorem setInitialFlag_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 7) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (setInitialFlag.take count) state) (setInitialFlag.getD count paddingOp) := by
  let core : List PackingOp := [.base (.base (.constant .old 1)), .base (.base (.minimum .total .old .total))]
  have ch : (runOps (rawIncidenceROM q full) core state).heap = state.heap := rfl
  apply prefix_access_append _ _ core (storeWorkspace 3) state ?_ ?_ count hc
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> trivial
  · intro count hc
    exact RawCandidateWorkspaceWordMacros.store_prefix_access q full 3 le_rfl _
      ((congrFun ch 8).trans hptr) count hc

theorem initializeLater_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (count : Nat) (hc : count ≤ 9) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (initializeLater.take count) state) := by
  let core : List PackingOp := loadCell .total 1 ++
    [.base (.base (.constant .old 1)), .base (.base (.add .total .total .old))]
  have cp : ∀ count ≤ core.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (core.take count) state) := by
    intro count hc
    change count ≤ 4 at hc
    interval_cases count <;> intro reg <;> cases reg <;>
      simp [core, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hf _ | apply scalar_fits; omega
  have cf := full_fit_of_prefix _ _ core state cp
  have ch : (runOps (rawIncidenceROM q full) core state).heap = state.heap := rfl
  exact prefix_fit_append _ _ core (storeWorkspace 2) state cp (by
    intro count hc
    exact RawCandidateWorkspaceWordMacros.store_prefix_fit q full 2 (by decide) _ cf
      ((congrFun ch 8).trans hptr) count hc) count hc

theorem initializeLater_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 9) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (initializeLater.take count) state) (initializeLater.getD count paddingOp) := by
  let core : List PackingOp := loadCell .total 1 ++
    [.base (.base (.constant .old 1)), .base (.base (.add .total .total .old))]
  have ch : (runOps (rawIncidenceROM q full) core state).heap = state.heap := rfl
  have hb := workspaceBase_ge full.length q
  have hw : 1 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  apply prefix_access_append _ _ core (storeWorkspace 2) state ?_ ?_ count hc
  · intro count hc
    change count < 4 at hc
    interval_cases count <;> simp [core, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hw]
  · intro count hc
    exact RawCandidateWorkspaceWordMacros.store_prefix_access q full 2 (by decide) _
      ((congrFun ch 8).trans hptr) count hc

private theorem setInitialFlag_heap (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) :
    (runOps (rawIncidenceROM q full) setInitialFlag state).heap =
      Function.update state.heap (workspaceBase full.length q + 3) (min 1 (state.register .total)) := by
  simp [setInitialFlag, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr]

theorem afterCard_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (h4 : state.heap 4 ≤ q)
    (count : Nat) (hc : count ≤ 26) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (afterCard.take count) state) := by
  let card := runOps (rawIncidenceROM q full) storeCard state
  let flagged := runOps (rawIncidenceROM q full) setInitialFlag card
  have hb := workspaceBase_ge full.length q
  have ch : card.heap = Function.update state.heap (cardAddress (workspaceBase full.length q) (state.heap 1)) (state.heap 4) := by
    simpa only [hptr] using storeCard_heap (rawIncidenceROM q full) state
  have cb : card.heap 8 = workspaceBase full.length q := by
    rw [ch]
    simp (disch := omega) [cardAddress, hptr]
  have c1 : card.heap 1 ≤ candidateCount full.length q := by
    rw [ch]
    simpa (disch := omega) [cardAddress] using h1
  have cp : ∀ count ≤ storeCard.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (storeCard.take count) state) :=
    fun count hc => storeCard_prefix_fit q full state hf hptr h1 h4 count hc
  have cf := full_fit_of_prefix _ _ storeCard state cp
  have fh : flagged.heap = Function.update card.heap (workspaceBase full.length q + 3) (min 1 (card.register .total)) :=
    setInitialFlag_heap q full card cb
  have fb : flagged.heap 8 = workspaceBase full.length q := by rw [fh]; simpa (disch := omega) using cb
  have f1 : flagged.heap 1 ≤ candidateCount full.length q := by rw [fh]; simpa (disch := omega) using c1
  have fp : ∀ count ≤ setInitialFlag.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (setInitialFlag.take count) card) :=
    fun count hc => setInitialFlag_prefix_fit q full card cf cb count hc
  have ff := full_fit_of_prefix _ _ setInitialFlag card fp
  apply prefix_fit_append _ _ storeCard (setInitialFlag ++ initializeLater) state cp ?_ count hc
  intro count hc
  apply prefix_fit_append _ _ setInitialFlag initializeLater card fp ?_ count hc
  intro count hc
  exact initializeLater_prefix_fit q full flagged ff fb f1 count hc

theorem afterCard_prefix_access (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (h1 : state.heap 1 ≤ candidateCount full.length q)
    (count : Nat) (hc : count < 26) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) (afterCard.take count) state) (afterCard.getD count paddingOp) := by
  let card := runOps (rawIncidenceROM q full) storeCard state
  let flagged := runOps (rawIncidenceROM q full) setInitialFlag card
  have hb := workspaceBase_ge full.length q
  have ch : card.heap = Function.update state.heap (cardAddress (workspaceBase full.length q) (state.heap 1)) (state.heap 4) := by
    simpa only [hptr] using storeCard_heap (rawIncidenceROM q full) state
  have cb : card.heap 8 = workspaceBase full.length q := by rw [ch]; simp (disch := omega) [cardAddress, hptr]
  have fh : flagged.heap = Function.update card.heap (workspaceBase full.length q + 3) (min 1 (card.register .total)) :=
    setInitialFlag_heap q full card cb
  have fb : flagged.heap 8 = workspaceBase full.length q := by rw [fh]; simpa (disch := omega) using cb
  apply prefix_access_append _ _ storeCard (setInitialFlag ++ initializeLater) state ?_ ?_ count hc
  · intro count hc
    exact storeCard_prefix_access q full state hptr h1 count hc
  · intro count hc
    apply prefix_access_append _ _ setInitialFlag initializeLater card ?_ ?_ count hc
    · intro count hc
      exact setInitialFlag_prefix_access q full card cb count hc
    · intro count hc
      exact initializeLater_prefix_access q full flagged fb count hc

theorem jump_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hexit : Fits (indexWidth 16 full.length q) (5 * target)) (count : Nat) (hc : count ≤ 3) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) ((jumpTo target).take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | exact hexit | exact RawCandidateWorkspaceWordMacros.small_constant_fits _ _ 0 (by decide)

theorem jump_prefix_access (q : Nat) (full : List (Finset (Fin q))) (target : Nat) (state : NatState)
    (count : Nat) (hc : count < 3) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((jumpTo target).take count) state) ((jumpTo target).getD count paddingOp) := by
  interval_cases count <;> trivial

theorem innerTail_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (h5 : state.heap 5 ≤ q) (h6 : state.heap 6 ≤ q) (hflag : state.heap (workspaceBase full.length q + 3) ≤ 1)
    (h2 : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) (count : Nat) (hc : count ≤ 32) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) ((innerTail start).take count) state) := by
  let flagged := runOps (rawIncidenceROM q full) updateFlag state
  let incremented := runOps (rawIncidenceROM q full) (incrementWorkspace 2) flagged
  have hb := workspaceBase_ge full.length q
  have fp : ∀ count ≤ updateFlag.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (updateFlag.take count) state) :=
    fun count hc => updateFlag_prefix_fit q full state hf hptr h5 h6 hflag count hc
  have ff := full_fit_of_prefix _ _ updateFlag state fp
  have fh : flagged.heap = Function.update state.heap (workspaceBase full.length q + 3)
      (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap (workspaceBase full.length q + 3)) :=
    updateFlag_heap _ _ _ hptr
  have fb : flagged.heap 8 = workspaceBase full.length q := by rw [fh]; simpa (disch := omega) using hptr
  have f2 : flagged.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q := by
    rw [fh]
    simpa using h2
  have fi : Fits (indexWidth 16 full.length q) (flagged.heap (workspaceBase full.length q + 2) + 1) :=
    scalar_fits _ _ _ (by omega)
  have ip : ∀ count ≤ (incrementWorkspace 2).length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace 2).take count) flagged) :=
    fun count hc => RawCandidateWorkspaceWordMacros.increment_prefix_fit q full 2 (by decide) flagged ff fb fi count hc
  have inf := full_fit_of_prefix _ _ (incrementWorkspace 2) flagged ip
  have hjump : Fits (indexWidth 16 full.length q) (5 * (start + 180)) := lt_of_le_of_lt (by omega) hend
  apply prefix_fit_append _ _ updateFlag (incrementWorkspace 2 ++ jumpTo (start + 180)) state fp ?_ count hc
  intro count hc
  apply prefix_fit_append _ _ (incrementWorkspace 2) (jumpTo (start + 180)) flagged ip ?_ count hc
  intro count hc
  exact jump_prefix_fit q full (start + 180) incremented inf hjump count hc

theorem innerTail_prefix_access (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q) (count : Nat) (hc : count < 32) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((innerTail start).take count) state) ((innerTail start).getD count paddingOp) := by
  let flagged := runOps (rawIncidenceROM q full) updateFlag state
  let incremented := runOps (rawIncidenceROM q full) (incrementWorkspace 2) flagged
  have hb := workspaceBase_ge full.length q
  have fh : flagged.heap = Function.update state.heap (workspaceBase full.length q + 3)
      (if state.heap 5 + state.heap 6 = 0 then 0 else state.heap (workspaceBase full.length q + 3)) :=
    updateFlag_heap _ _ _ hptr
  have fb : flagged.heap 8 = workspaceBase full.length q := by rw [fh]; simpa (disch := omega) using hptr
  apply prefix_access_append _ _ updateFlag (incrementWorkspace 2 ++ jumpTo (start + 180)) state ?_ ?_ count hc
  · intro count hc
    exact updateFlag_prefix_access q full state hptr count hc
  · intro count hc
    apply prefix_access_append _ _ (incrementWorkspace 2) (jumpTo (start + 180)) flagged ?_ ?_ count hc
    · intro count hc
      exact RawCandidateWorkspaceWordMacros.increment_prefix_access q full 2 (by decide) flagged fb count hc
    · intro count hc
      exact jump_prefix_access q full (start + 180) incremented count hc

theorem finishCandidate_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hptr : state.heap 8 = workspaceBase full.length q)
    (hM : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (hcounter : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hflag : state.heap (workspaceBase full.length q + 3) ≤ 1)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) (count : Nat) (hc : count ≤ 34) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) ((finishCandidate start).take count) state) := by
  let kept := runOps (rawIncidenceROM q full) storeKeep state
  let incremented := runOps (rawIncidenceROM q full) (incrementWorkspace 1) kept
  have hb := workspaceBase_ge full.length q
  have kp : ∀ count ≤ storeKeep.length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) (storeKeep.take count) state) :=
    fun count hc => storeKeep_prefix_fit q full state hf hptr hM h1 hflag count hc
  have kf := full_fit_of_prefix _ _ storeKeep state kp
  have kh : kept.heap = Function.update state.heap
      (keepAddress (workspaceBase full.length q) (candidateCount full.length q) (state.heap 1))
      (state.heap (workspaceBase full.length q + 3)) := by
    simpa only [hM] using storeKeep_heap (rawIncidenceROM q full) (workspaceBase full.length q) state hptr
  have kb : kept.heap 8 = workspaceBase full.length q := by rw [kh]; simpa (disch := omega) [keepAddress] using hptr
  have k1 : kept.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q := by
    rw [kh]
    simpa (disch := omega) [keepAddress] using hcounter
  have ki : Fits (indexWidth 16 full.length q) (kept.heap (workspaceBase full.length q + 1) + 1) :=
    scalar_fits _ _ _ (by omega)
  have ip : ∀ count ≤ (incrementWorkspace 1).length, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace 1).take count) kept) :=
    fun count hc => RawCandidateWorkspaceWordMacros.increment_prefix_fit q full 1 (by decide) kept kf kb ki count hc
  have inf := full_fit_of_prefix _ _ (incrementWorkspace 1) kept ip
  have hjump : Fits (indexWidth 16 full.length q) (5 * (start + 6)) := lt_of_le_of_lt (by omega) hend
  apply prefix_fit_append _ _ storeKeep (incrementWorkspace 1 ++ jumpTo (start + 6)) state kp ?_ count hc
  intro count hc
  apply prefix_fit_append _ _ (incrementWorkspace 1) (jumpTo (start + 6)) kept ip ?_ count hc
  intro count hc
  exact jump_prefix_fit q full (start + 6) incremented inf hjump count hc

theorem finishCandidate_prefix_access (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hM : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (h1 : state.heap 1 ≤ candidateCount full.length q) (count : Nat) (hc : count < 34) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((finishCandidate start).take count) state) ((finishCandidate start).getD count paddingOp) := by
  let kept := runOps (rawIncidenceROM q full) storeKeep state
  let incremented := runOps (rawIncidenceROM q full) (incrementWorkspace 1) kept
  have hb := workspaceBase_ge full.length q
  have kh : kept.heap = Function.update state.heap
      (keepAddress (workspaceBase full.length q) (candidateCount full.length q) (state.heap 1))
      (state.heap (workspaceBase full.length q + 3)) := by
    simpa only [hM] using storeKeep_heap (rawIncidenceROM q full) (workspaceBase full.length q) state hptr
  have kb : kept.heap 8 = workspaceBase full.length q := by rw [kh]; simpa (disch := omega) [keepAddress] using hptr
  apply prefix_access_append _ _ storeKeep (incrementWorkspace 1 ++ jumpTo (start + 6)) state ?_ ?_ count hc
  · intro count hc
    exact storeKeep_prefix_access q full state hptr hM h1 count hc
  · intro count hc
    apply prefix_access_append _ _ (incrementWorkspace 1) (jumpTo (start + 6)) kept ?_ ?_ count hc
    · intro count hc
      exact RawCandidateWorkspaceWordMacros.increment_prefix_access q full 1 (by decide) kept kb count hc
    · intro count hc
      exact jump_prefix_access q full (start + 6) incremented count hc

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordDataPieces
