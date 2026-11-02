module

public import PaperProofs.Structure.RawCandidateSerializedChildrenRAM
public import PaperProofs.Structure.RawCandidateSerializedInputWordCache
import Mathlib.Tactic.IntervalCases

/-! Bounds for the existing children serializer's parent and flat-counter
addresses.  Each address is recomputed from raw ROM, with arbitrary heap
cell eight.  Read bounds are ordinary current-cell bounds. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordAddress

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount candidateCount_fits workspaceBase_ge)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits)
open RawCandidateSerializedChildrenRAM
open RawCandidateSerializedInputRAM (loadCache recovered base_runOps loadCache_runOps)
open RawCandidateSerializedInputWordCache (base_safe loadCache_safe)
open RawCandidateOrderingWord (MacroSafe constant_safe single_safe)
open RawIncidenceScanSafety (NatAccessFits)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

def flatLead : List PackingOp :=
  [.base (.base (.constant .index 5)), .arithmetic .multiply .index .total .index,
   .base (.base (.add .address .address .index)), .base (.base (.constant .index 5)),
   .base (.base (.add .address .address .index))]

def parentLead : List PackingOp :=
  [.base (.base (.constant .index 4)), .arithmetic .multiply .index .total .index,
   .base (.base (.add .address .address .index)), .base (.base (.constant .index 5)),
   .base (.base (.add .address .address .index)), .base (.base (.add .address .address .old))]

private theorem flatLead_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ha : state.register .address = workspaceBase full.length q)
    (ht : state.register .total = candidateCount full.length q) (count : Nat) (hc : count ≤ 5) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (flatLead.take count) state) := by
  have hb := workspaceBase_ge full.length q
  have hl := workspaceLimit_fits full.length q
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 5 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 5; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (flatLead[count]'(by change count < 5; exact hc')) _)
    interval_cases count <;>
      simp only [flatLead, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
        natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
      | (simp_all [flatLead, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)

private theorem parentLead_fit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ha : state.register .address = workspaceBase full.length q)
    (ht : state.register .total = candidateCount full.length q)
    (ho : state.register .old ≤ candidateCount full.length q) (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (parentLead.take count) state) := by
  have hb := workspaceBase_ge full.length q
  have hl := workspaceLimit_fits full.length q
  induction count with
  | zero => exact hf
  | succ count ih =>
    have hc' : count < 6 := by omega
    have hp := ih hc'.le
    rw [List.take_succ_eq_append_getElem (by change count < 6; exact hc'), runOps_append]
    change RegistersFit _ (natExecuteOp _ (parentLead[count]'(by change count < 6; exact hc')) _)
    interval_cases count <;>
      simp only [parentLead, List.getElem_cons_zero, List.getElem_cons_succ, RegistersFit,
        natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)
      | (simp_all [parentLead, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hl; unfold workspaceLimit; omega)

private theorem flatLead_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ha : state.register .address = workspaceBase full.length q)
    (ht : state.register .total = candidateCount full.length q) : MacroSafe q full flatLead state := by
  constructor
  · exact fun count hc => flatLead_fit q full state hf ha ht count hc
  · intro count hc
    have hc' : count < 5 := hc
    interval_cases count <;> trivial

private theorem parentLead_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ha : state.register .address = workspaceBase full.length q)
    (ht : state.register .total = candidateCount full.length q)
    (ho : state.register .old ≤ candidateCount full.length q) : MacroSafe q full parentLead state := by
  constructor
  · exact fun count hc => parentLead_fit q full state hf ha ht ho count hc
  · intro count hc
    have hc' : count < 6 := hc
    interval_cases count <;> trivial

theorem loadFlat_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hread : Fits (indexWidth 16 full.length q) (state.heap (flatAddress full.length q))) :
    MacroSafe q full (loadFlat target) state := by
  let rom := rawIncidenceROM q full
  let base := runOps rom RawCandidateWorkspaceBaseRAM.program state
  have b := base_safe q full state hf
  have br : base = recovered full.length q state := base_runOps q full state
  have ba : base.register .address = workspaceBase full.length q := by rw [br]; rfl
  have bt : base.register .total = candidateCount full.length q := by rw [br]; rfl
  have a := flatLead_safe q full base b.full ba bt
  let addressed := runOps rom flatLead base
  have ha : addressed.register .address = flatAddress full.length q := by
    simp [addressed, flatLead, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      ba, bt, flatAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  have l := single_safe q full (.base (.base (.loadHeap target .address))) addressed a.full
    (by apply fits_update a.full; change Fits _ (state.heap (addressed.register .address)); rw [ha]; exact hread)
    (by change addressed.register .address < workspaceLimit full.length q; rw [ha]; unfold flatAddress workspaceLimit; omega)
  simpa only [loadFlat, flatLead, List.cons_append, List.nil_append] using b.append (a.append l)

theorem storeFlat_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) : MacroSafe q full storeFlat state := by
  let rom := rawIncidenceROM q full
  let base := runOps rom RawCandidateWorkspaceBaseRAM.program state
  have b := base_safe q full state hf
  have br : base = recovered full.length q state := base_runOps q full state
  have ba : base.register .address = workspaceBase full.length q := by rw [br]; rfl
  have bt : base.register .total = candidateCount full.length q := by rw [br]; rfl
  have a := flatLead_safe q full base b.full ba bt
  let addressed := runOps rom flatLead base
  have ha : addressed.register .address = flatAddress full.length q := by
    simp [addressed, flatLead, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      ba, bt, flatAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  have s := single_safe q full (.base (.base (.storeHeap .address .value))) addressed a.full a.full
    (by change addressed.register .address < workspaceLimit full.length q; rw [ha]; unfold flatAddress workspaceLimit; omega)
  simpa only [storeFlat, flatLead, List.cons_append, List.nil_append] using b.append (a.append s)

theorem setFlat_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) : MacroSafe q full setFlat state := by
  have c := constant_safe q full .value 0 state hf (RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by omega))
  exact c.append (storeFlat_safe q full _ c.full)

theorem incrementFlat_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (flatAddress full.length q) + 1)) :
    MacroSafe q full incrementFlat state := by
  let rom := rawIncidenceROM q full
  have l := loadFlat_safe q full .value state hf ((Nat.le_succ _).trans_lt hinc)
  let loaded := runOps rom (loadFlat .value) state
  have hv : loaded.register .value = state.heap (flatAddress full.length q) := by
    dsimp only [loaded]
    rw [loadFlat_runOps]
    simp [flatLoaded]
  have c := constant_safe q full .index 1 loaded l.full (RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by omega))
  have a := single_safe q full (.base (.base (.add .value .value .index))) _ c.full
    (by apply fits_update c.full; change Fits _ (loaded.register .value + 1); rw [hv]; exact hinc) (by trivial)
  have s := storeFlat_safe q full _ a.full
  simpa only [incrementFlat, List.append_assoc, List.cons_append, List.nil_append] using l.append (c.append (a.append s))

theorem loadParent_safe (q : Nat) (full : List (Finset (Fin q))) (counter : Nat) (hoff : counter ≤ 3)
    (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hc : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (hr : Fits (indexWidth 16 full.length q)
      (state.heap (parentAddress full.length q (state.heap (workspaceBase full.length q + counter))))) :
    MacroSafe q full (loadParent counter) state := by
  let rom := rawIncidenceROM q full
  have l := loadCache_safe q full .old counter hoff state hf (hc.trans_lt (candidateCount_fits _ _))
  let loaded := runOps rom (loadCache .old counter) state
  have lo : loaded.register .old = state.heap (workspaceBase full.length q + counter) := by
    dsimp only [loaded]
    rw [loadCache_runOps]
    simp [RawCandidateSerializedInputRAM.loaded]
  have b := base_safe q full loaded l.full
  let base := runOps rom RawCandidateWorkspaceBaseRAM.program loaded
  have br : base = recovered full.length q loaded := base_runOps q full loaded
  have ba : base.register .address = workspaceBase full.length q := by rw [br]; rfl
  have bt : base.register .total = candidateCount full.length q := by rw [br]; rfl
  have bo : base.register .old = state.heap (workspaceBase full.length q + counter) := by rw [br]; exact lo
  have a := parentLead_safe q full base b.full ba bt (by rw [bo]; exact hc)
  let addressed := runOps rom parentLead base
  have ha : addressed.register .address = parentAddress full.length q (state.heap (workspaceBase full.length q + counter)) := by
    simp [addressed, parentLead, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      ba, bt, bo, parentAddress, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  have f := single_safe q full (.base (.base (.loadHeap .value .address))) addressed a.full
    (by apply fits_update a.full; change Fits _ (state.heap (addressed.register .address)); rw [ha]; exact hr)
    (by change addressed.register .address < workspaceLimit full.length q; rw [ha]; unfold parentAddress workspaceLimit; omega)
  simpa only [loadParent, parentLead, List.append_assoc, List.cons_append, List.nil_append] using l.append (b.append (a.append f))

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordAddress
