module

public import PaperProofs.Structure.RawCandidateSerializedInputWordPieces
import Mathlib.Tactic.IntervalCases

/-! The original 79-op header block, composed as 18+2+8+2+15+15+19.
Only the ordinary initial node-count cell bound is supplied. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordHeaders

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount candidateCount_fits workspaceBase_ge)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawCandidateSerializedInputRAM
open RawCandidateSerializedInputWordCache (storeCache_safe loadCache_safe)
open RawCandidateSerializedInputWordPieces (loadNodeCount_safe loadCache_heap)
open RawCandidateOrderingWord (MacroSafe single_safe storeCell_safe)
open RawIncidenceScanSafety (NatAccessFits)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

private def dims : List PackingOp :=
  [.base (.base (.constant .index 0)), .base (.base (.loadROM .input .old .index)),
   .base (.base (.constant .index 1)), .base (.base (.loadROM .input .fresh .index))] ++
    storeCell .old 3 ++ storeCell .fresh 4

private def product : List PackingOp :=
  [.arithmetic .multiply .total .old .fresh, .base (.base (.minimum .value .total .total))]

private def tailCode : List PackingOp :=
  loadCell .old 5 ++
    [.arithmetic .multiply .old .old .fresh, .base (.base (.add .total .total .old)),
     .base (.base (.constant .index 3)), .base (.base (.add .total .total .index))] ++ storeCell .total 0 ++
    loadCell .total 5 ++ [.base (.base (.add .total .total .total))] ++ storeCell .total 1 ++
    loadCell .total 5 ++ [.base (.base (.constant .index 1)), .base (.subtract .total .total .index)] ++ storeCell .total 2

private theorem dims_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (count : Nat) (hc : count ≤ 8) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (dims.take count) state) := by
  have hl := workspaceLimit_fits full.length q
  have hN : full.length ≤ candidateCount full.length q := by unfold candidateCount; omega
  have hq : q ≤ candidateCount full.length q := by unfold candidateCount; omega
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 8 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 8; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (dims[count]'(by change count < 8; exact hc')) _)
    interval_cases count <;>
      simp only [dims, storeCell, List.getElem_append, List.getElem_cons_zero, List.getElem_cons_succ,
        List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
      | (simp_all [dims, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q];
          apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)

private theorem dims_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) : MacroSafe q full dims state := by
  constructor
  · exact fun count hc => dims_fit q full state hf count hc
  · intro count hc
    have hc' : count < 8 := hc
    interval_cases count <;>
      simp [dims, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals first | (rw [raw_input_length]; omega) | (unfold workspaceLimit; omega)

private theorem dims_values (q : Nat) (full : List (Finset (Fin q))) (state : NatState) :
    let after := runOps (rawIncidenceROM q full) dims state
    after.register .old = full.length ∧ after.register .fresh = q ∧
      after.heap = Function.update (Function.update state.heap 3 full.length) 4 q := by
  simp [dims, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_N, raw_header_q]

private theorem product_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ho : state.register .old = full.length) (hh : state.register .fresh = q) : MacroSafe q full product state := by
  have hprod : Fits (indexWidth 16 full.length q) (full.length * q) := by
    apply workspace_address_fits
    unfold workspaceLimit workspaceBase candidateCount
    nlinarith
  have a := single_safe q full (.arithmetic .multiply .total .old .fresh) state hf
    (by apply fits_update hf; change Fits _ (state.register .old * state.register .fresh); rw [ho, hh]; exact hprod)
    (by trivial)
  have b := single_safe q full (.base (.base (.minimum .value .total .total))) _ a.full
    (by apply fits_update a.full; exact (Nat.min_le_left _ _).trans_lt (a.full .total)) (by trivial)
  simpa only [product, List.cons_append, List.nil_append] using a.append b

private theorem tail_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hh : state.register .fresh = q) (ht : state.register .total = full.length * q)
    (h5 : state.heap 5 ≤ candidateCount full.length q) (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (tailCode.take count) state) := by
  have hl := workspaceLimit_fits full.length q
  have hm : full.length ≤ candidateCount full.length q := by unfold candidateCount; omega
  have hnq := Nat.mul_le_mul_right q hm
  have h5q := Nat.mul_le_mul_right q h5
  have hb : 8 * (candidateCount full.length q * q) + 16 = workspaceBase full.length q := by
    unfold workspaceBase
    ring
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 19 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (tailCode[count]'(by change count < 19; exact hc')) _)
    interval_cases count <;>
      simp only [tailCode, loadCell, storeCell, List.getElem_append, List.getElem_cons_zero, List.getElem_cons_succ,
        List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
      | (simp_all [tailCode, loadCell, storeCell, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)

private theorem tail_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hh : state.register .fresh = q) (ht : state.register .total = full.length * q)
    (h5 : state.heap 5 ≤ candidateCount full.length q) : MacroSafe q full tailCode state := by
  constructor
  · exact fun count hc => tail_fit q full state hf hh ht h5 count hc
  · intro count hc
    have hc' : count < 19 := hc
    interval_cases count <;>
      simp [tailCode, loadCell, storeCell, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals unfold workspaceLimit
    all_goals omega

theorem headers_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hcount : state.heap (nodeCountAddress full.length q) ≤ candidateCount full.length q) :
    MacroSafe q full headers state := by
  let rom := rawIncidenceROM q full
  have a := loadNodeCount_safe q full state hf (hcount.trans_lt (candidateCount_fits _ _))
  let counted := runOps rom loadNodeCount state
  have cv : counted.register .value = state.heap (nodeCountAddress full.length q) := (loadNodeCount_values q full state).1
  have b := storeCell_safe q full .value 5 (by omega) counted a.full
  let saved := runOps rom (storeCell .value 5) counted
  have sh5 : saved.heap 5 = state.heap (nodeCountAddress full.length q) := by
    simp [saved, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, cv]
  have c := dims_safe q full saved b.full
  let dimensional := runOps rom dims saved
  have dv : dimensional.register .old = full.length ∧ dimensional.register .fresh = q ∧
      dimensional.heap = Function.update (Function.update saved.heap 3 full.length) 4 q := dims_values q full saved
  have d := product_safe q full dimensional c.full dv.1 dv.2.1
  let multiplied := runOps rom product dimensional
  have pv : multiplied.register .value = full.length * q := by
    simp [multiplied, product, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, dv.1, dv.2.1]
  have pf : multiplied.register .fresh = q := by
    simpa [multiplied, product, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute] using dv.2.1
  have ph : multiplied.heap = dimensional.heap := rfl
  have e := storeCache_safe q full 3 (by omega) multiplied d.full
  let cached := runOps rom (storeCache 3) multiplied
  have ch : cached.heap = Function.update multiplied.heap (workspaceBase full.length q + 3) (full.length * q) := by
    dsimp only [cached]
    rw [storeCache_runOps]
    simp only [stored, pv]
  have cb : cached.heap (workspaceBase full.length q + 3) = full.length * q := by rw [ch]; simp
  have cp : Fits (indexWidth 16 full.length q) (cached.heap (workspaceBase full.length q + 3)) := by
    rw [cb]
    apply workspace_address_fits
    unfold workspaceLimit workspaceBase candidateCount
    nlinarith
  have f := loadCache_safe q full .total 3 (by omega) cached e.full cp
  let loaded := runOps rom (loadCache .total 3) cached
  have lt : loaded.register .total = full.length * q := by
    dsimp only [loaded]
    rw [loadCache_runOps]
    simpa [RawCandidateSerializedInputRAM.loaded] using cb
  have lf : loaded.register .fresh = q := by
    dsimp only [loaded, cached]
    rw [loadCache_runOps, storeCache_runOps]
    simpa [RawCandidateSerializedInputRAM.loaded, stored, recovered] using pf
  have l5 : loaded.heap 5 ≤ candidateCount full.length q := by
    have hb := workspaceBase_ge full.length q
    rw [loadCache_heap q full .total 3 cached, ch,
      Function.update_of_ne (by omega), ph, dv.2.2]
    simpa only [Function.update_of_ne (by decide : (5 : Nat) ≠ 4),
      Function.update_of_ne (by decide : (5 : Nat) ≠ 3), sh5] using hcount
  have g := tail_safe q full loaded f.full lf lt l5
  simpa only [headers, dims, product, tailCode, List.append_assoc, List.cons_append, List.nil_append] using
    a.append (b.append (c.append (d.append (e.append (f.append g)))))

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordHeaders
