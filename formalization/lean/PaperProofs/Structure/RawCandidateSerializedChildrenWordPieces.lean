module

public import PaperProofs.Structure.RawCandidateSerializedChildrenWordAddress
public import PaperProofs.Structure.RawCandidateSerializedInputWordPieces

/-! Actual child-list serialization pieces, bounded by ordinary current
headers and counters. Physical bounds do not assume a written output prefix,
parent answer, future safe execution, or a persistent heap-eight pointer. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordPieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawCandidateSerializedChildrenRAM
open RawCandidateSerializedInputRAM (loadCache setCache incrementCache recovered loadCache_runOps incrementCache_heap)
open RawCandidateSerializedInputWordCache (loadCache_safe setCache_safe incrementCache_safe)
open RawCandidateSerializedChildrenWordAddress
open RawCandidateOrderingWord (MacroSafe single_safe constant_safe loadCell_safe jump_safe)
open RawIncidenceScanSafety (NatAccessFits)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

private theorem scalar_fits (N q value : Nat) (hv : value ≤ workspaceBase N q + 4 * candidateCount N q + 32) :
    Fits (indexWidth 16 N q) value := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

private def parentTail : List PackingOp :=
  [.base (.base (.constant .address 3)), .base (.base (.add .address .address .fresh)),
   .base (.base (.add .address .address .old)), .base (.base (.storeHeap .address .value))]

private def childTail : List PackingOp :=
  [.base (.base (.add .address .old .total)), .base (.base (.constant .index 3)),
   .base (.base (.add .address .address .index)), .base (.base (.add .address .address .value)),
   .base (.base (.storeHeap .address .fresh))]

private def degreeTail : List PackingOp :=
  [.base (.base (.add .address .total .fresh)), .base (.base (.constant .index 3)),
   .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old)),
   .base (.base (.storeHeap .address .value))]

private theorem parentTail_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ho : state.register .old ≤ candidateCount full.length q)
    (hh : state.register .fresh ≤ workspaceBase full.length q) : MacroSafe q full parentTail state := by
  have hl := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 4 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hc'' : count < 4 := by omega
      have hp := ih hc''.le hc''.le
      rw [List.take_succ_eq_append_getElem (by change count < 4; exact hc''), runOps_append]
      change RegistersFit _ (natExecuteOp _ (parentTail[count]'(by change count < 4; exact hc'')) _)
      interval_cases count <;>
        simp only [parentTail, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals first
        | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
        | (simp_all [parentTail, runOps, natExecuteOp, Op.execute, Instruction.execute];
            apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 4 := hc
    interval_cases count <;>
      simp [parentTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold workspaceLimit
    all_goals omega

private theorem childTail_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ho : state.register .old ≤ workspaceBase full.length q)
    (ht : state.register .total ≤ 2 * candidateCount full.length q)
    (hv : state.register .value ≤ candidateCount full.length q) : MacroSafe q full childTail state := by
  have hl := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 5 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hc'' : count < 5 := by omega
      have hp := ih hc''.le hc''.le
      rw [List.take_succ_eq_append_getElem (by change count < 5; exact hc''), runOps_append]
      change RegistersFit _ (natExecuteOp _ (childTail[count]'(by change count < 5; exact hc'')) _)
      interval_cases count <;>
        simp only [childTail, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals first
        | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
        | (simp_all [childTail, runOps, natExecuteOp, Op.execute, Instruction.execute];
            apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 5 := hc
    interval_cases count <;>
      simp [childTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold workspaceLimit
    all_goals omega

private theorem degreeTail_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ht : state.register .total ≤ workspaceBase full.length q)
    (hh : state.register .fresh ≤ candidateCount full.length q)
    (ho : state.register .old ≤ candidateCount full.length q) : MacroSafe q full degreeTail state := by
  have hl := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 5 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hc'' : count < 5 := by omega
      have hp := ih hc''.le hc''.le
      rw [List.take_succ_eq_append_getElem (by change count < 5; exact hc''), runOps_append]
      change RegistersFit _ (natExecuteOp _ (degreeTail[count]'(by change count < 5; exact hc'')) _)
      interval_cases count <;>
        simp only [degreeTail, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals first
        | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
        | (simp_all [degreeTail, runOps, natExecuteOp, Op.execute, Instruction.execute];
            apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 5 := hc
    interval_cases count <;>
      simp [degreeTail, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold workspaceLimit
    all_goals omega

theorem initBlock_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) : MacroSafe q full initBlock state := by
  have a := setCache_safe q full 1 0 (by omega) state hf (scalar_fits _ _ _ (by omega))
  exact a.append (setFlat_safe q full _ a.full)

theorem writeParent_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hn : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (hp : Fits (indexWidth 16 full.length q)
      (state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 1))))) :
    MacroSafe q full writeParent state := by
  let rom := rawIncidenceROM q full
  have a := loadParent_safe q full 1 (by omega) state hf hn hp
  let loaded := runOps rom (loadParent 1) state
  have b := loadCell_safe q full .fresh 0 (by omega) loaded a.full (scalar_fits _ _ (state.heap 0) (h0.trans (by omega)))
  let prepared := runOps rom (loadCell .fresh 0) loaded
  have ho : prepared.register .old = state.heap (workspaceBase full.length q + 1) := by
    dsimp only [prepared, loaded]
    rw [loadParent_runOps]
    simp [parentLoaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  have hh : prepared.register .fresh = state.heap 0 := by
    dsimp only [prepared, loaded]
    rw [loadParent_runOps]
    simp [parentLoaded, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  have t := parentTail_safe q full prepared b.full (by rw [ho]; exact hn) (by rw [hh]; exact h0)
  simpa only [writeParent, parentTail, List.append_assoc] using a.append (b.append t)

theorem initRow_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hn : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (hp : Fits (indexWidth 16 full.length q)
      (state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 1))))) :
    MacroSafe q full initRow state := by
  have a := writeParent_safe q full state hf hn h0 hp
  have b := setCache_safe q full 3 0 (by omega) _ a.full (scalar_fits _ _ _ (by omega))
  have c := setCache_safe q full 2 0 (by omega) _ b.full (scalar_fits _ _ _ (by omega))
  simpa only [initRow, List.append_assoc] using a.append (b.append c)

theorem writeChild_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hc : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hflat : state.heap (flatAddress full.length q) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (h1 : state.heap 1 ≤ 2 * candidateCount full.length q) : MacroSafe q full writeChild state := by
  let rom := rawIncidenceROM q full
  have a := loadCache_safe q full .fresh 2 (by omega) state hf (hc.trans_lt (candidateCount_fits _ _))
  let s1 := runOps rom (loadCache .fresh 2) state
  have b := loadFlat_safe q full .value s1 a.full (hflat.trans_lt (candidateCount_fits _ _))
  let s2 := runOps rom (loadFlat .value) s1
  have c := loadCell_safe q full .old 0 (by omega) s2 b.full (scalar_fits _ _ (state.heap 0) (h0.trans (by omega)))
  let s3 := runOps rom (loadCell .old 0) s2
  have d := loadCell_safe q full .total 1 (by omega) s3 c.full (scalar_fits _ _ (state.heap 1) (h1.trans (by omega)))
  let prepared := runOps rom (loadCell .total 1) s3
  have hv : prepared.register .old = state.heap 0 ∧ prepared.register .total = state.heap 1 ∧
      prepared.register .value = state.heap (flatAddress full.length q) := by
    dsimp only [prepared, s3, s2, s1]
    rw [loadFlat_runOps, loadCache_runOps]
    simp [RawCandidateSerializedInputRAM.loaded, flatLoaded, recovered, loadCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute]
  have t := childTail_safe q full prepared d.full
    (by rw [hv.1]; exact h0) (by rw [hv.2.1]; exact h1) (by rw [hv.2.2]; exact hflat)
  simpa only [writeChild, childTail, List.append_assoc] using a.append (b.append (c.append (d.append t)))

theorem writeDegree_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hn : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hd : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (h5 : state.heap 5 ≤ candidateCount full.length q) : MacroSafe q full writeDegree state := by
  let rom := rawIncidenceROM q full
  have a := loadCache_safe q full .value 3 (by omega) state hf (hd.trans_lt (candidateCount_fits _ _))
  let s1 := runOps rom (loadCache .value 3) state
  have b := loadCache_safe q full .old 1 (by omega) s1 a.full (hn.trans_lt (candidateCount_fits _ _))
  let s2 := runOps rom (loadCache .old 1) s1
  have c := loadCell_safe q full .fresh 5 (by omega) s2 b.full (h5.trans_lt (candidateCount_fits _ _))
  let s3 := runOps rom (loadCell .fresh 5) s2
  have d := loadCell_safe q full .total 0 (by omega) s3 c.full (scalar_fits _ _ (state.heap 0) (h0.trans (by omega)))
  let prepared := runOps rom (loadCell .total 0) s3
  have hv : prepared.register .total = state.heap 0 ∧ prepared.register .fresh = state.heap 5 ∧
      prepared.register .old = state.heap (workspaceBase full.length q + 1) := by
    dsimp only [prepared, s3, s2, s1]
    rw [loadCache_runOps, loadCache_runOps]
    simp [RawCandidateSerializedInputRAM.loaded, recovered, loadCell, runOps,
      natExecuteOp, Op.execute, Instruction.execute]
  have t := degreeTail_safe q full prepared d.full
    (by rw [hv.1]; exact h0) (by rw [hv.2.1]; exact h5) (by rw [hv.2.2]; exact hn)
  simpa only [writeDegree, degreeTail, List.append_assoc] using a.append (b.append (c.append (d.append t)))

private def matchTail (start : Nat) : List PackingOp :=
  [.base (.base (.constant .index 1)), .base (.base (.add .old .old .index)),
   .base (.subtract .flag .value .old), .base (.subtract .total .old .value),
   .base (.base (.add .flag .flag .total)), .base (.base (.constant .index (5 * (start + 206)))),
   .jumpIfZero .flag .index]

private theorem matchTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ho : state.register .old ≤ candidateCount full.length q)
    (hv : state.register .value ≤ candidateCount full.length q)
    (hexit : Fits (indexWidth 16 full.length q) (5 * (start + 206))) :
    MacroSafe q full (matchTail start) state := by
  have hl := workspaceLimit_fits full.length q
  constructor
  · intro count hc
    have hc' : count ≤ 7 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hc'' : count < 7 := by omega
      have hp := ih hc''.le hc''.le
      rw [List.take_succ_eq_append_getElem (by change count < 7; exact hc''), runOps_append]
      change RegistersFit _ (natExecuteOp _ ((matchTail start)[count]'(by change count < 7; exact hc'')) _)
      interval_cases count <;>
        simp only [matchTail, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
          natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals first
        | exact hexit
        | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
        | (simp_all [matchTail, runOps, natExecuteOp, Op.execute, Instruction.execute];
            apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
  · intro count hc
    have hc' : count < 7 := hc
    interval_cases count <;> trivial

theorem matchTest_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hn : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hc : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hp : state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 2))) ≤ candidateCount full.length q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    MacroSafe q full (matchTest start) state := by
  let rom := rawIncidenceROM q full
  have a := loadParent_safe q full 2 (by omega) state hf hc (hp.trans_lt (candidateCount_fits _ _))
  let loaded := runOps rom (loadParent 2) state
  have b := loadCache_safe q full .old 1 (by omega) loaded a.full (hn.trans_lt (candidateCount_fits _ _))
  let prepared := runOps rom (loadCache .old 1) loaded
  have h : prepared.register .old = state.heap (workspaceBase full.length q + 1) ∧
      prepared.register .value = state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + 2))) := by
    dsimp only [prepared, loaded]
    rw [loadCache_runOps, loadParent_runOps]
    simp [RawCandidateSerializedInputRAM.loaded, recovered, parentLoaded]
  have t := matchTail_safe q full start prepared b.full
    (by rw [h.1]; exact hn) (by rw [h.2]; exact hp) (lt_of_le_of_lt (by omega) hend)
  simpa only [matchTest, matchLead, matchTail, List.append_assoc, List.cons_append, List.nil_append] using a.append (b.append t)

private theorem update_bound (heap : Nat → Nat) (address value target bound : Nat)
    (hv : value ≤ bound) (ht : heap target ≤ bound) : Function.update heap address value target ≤ bound := by
  by_cases heq : target = address
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using ht

theorem matched_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hc : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hd : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (hflat : state.heap (flatAddress full.length q) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (h1 : state.heap 1 ≤ 2 * candidateCount full.length q) : MacroSafe q full matched state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have a := writeChild_safe q full state hf hc hflat h0 h1
  let written := runOps rom writeChild state
  have wh : written.heap = Function.update state.heap
      (3 + state.heap 0 + state.heap 1 + state.heap (flatAddress full.length q))
      (state.heap (B + 2)) := writeChild_heap q full state
  have wd : written.heap (B + 3) ≤ M := by rw [wh]; exact update_bound _ _ _ _ _ hc hd
  have wf : written.heap (flatAddress full.length q) ≤ M := by rw [wh]; exact update_bound _ _ _ _ _ hc hflat
  have c := incrementCache_safe q full 3 (by omega) written a.full
    (scalar_fits _ _ _ (by have hd' : written.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q := wd; omega))
  let counted := runOps rom (incrementCache 3) written
  have ch : counted.heap = Function.update written.heap (B + 3) (written.heap (B + 3) + 1) :=
    incrementCache_heap q full 3 written
  have cf : counted.heap (flatAddress full.length q) ≤ candidateCount full.length q := by
    rw [ch, Function.update_of_ne (by unfold flatAddress; dsimp only [B]; omega)]
    exact wf
  have f := incrementFlat_safe q full counted c.full (scalar_fits _ _ _ (by omega))
  simpa only [matched, List.append_assoc] using a.append (c.append f)

theorem innerTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hc : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    MacroSafe q full (innerTail start) state := by
  have a := incrementCache_safe q full 2 (by omega) state hf (scalar_fits _ _ _ (by omega))
  have b := jump_safe q full (start + 127) _ a.full (lt_of_le_of_lt (by omega) hend)
  simpa only [innerTail, innerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append] using a.append b

theorem outerTail_safe (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hn : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hd : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (h0 : state.heap 0 ≤ workspaceBase full.length q)
    (h5 : state.heap 5 ≤ candidateCount full.length q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) :
    MacroSafe q full (outerTail start) state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  have a := writeDegree_safe q full state hf hn hd h0 h5
  let written := runOps rom writeDegree state
  have wh : written.heap = Function.update state.heap (3 + state.heap 0 + state.heap 5 + state.heap (B + 1))
      (state.heap (B + 3)) := writeDegree_heap q full state
  have wn : written.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q := by
    rw [wh]
    exact update_bound _ _ _ _ _ hd hn
  have b := incrementCache_safe q full 1 (by omega) written a.full (scalar_fits _ _ _ (by omega))
  have c := jump_safe q full (start + 35) _ b.full (lt_of_le_of_lt (by omega) hend)
  simpa only [outerTail, outerLead, jumpTo, List.take_succ_cons, List.take_zero,
    List.append_assoc, List.cons_append, List.nil_append] using a.append (b.append c)

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordPieces
