module

public import PaperProofs.Structure.RawCandidateSerializedInputRAM
public import PaperProofs.Structure.RawCandidateWorkspaceBaseWord
public import PaperProofs.Structure.RawCandidateOrderingWord

/-! Prefix safety for the original serializer cache accesses.  Every access
recomputes B with the original twelve instructions, so the mutable heap,
including serialized output cell 8, is arbitrary. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordCache

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount)
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawCandidateSerializedInputRAM
open RawCandidateOrderingWord (MacroSafe constant_safe single_safe)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

theorem base_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) :
    MacroSafe q full RawCandidateWorkspaceBaseRAM.program state := by
  constructor
  · intro count hc
    exact RawCandidateWorkspaceBaseWord.runOps_prefix_registersFit q full state hf count hc
  · intro count hc
    rw [List.getD_eq_getElem _ _ hc]
    exact RawCandidateWorkspaceBaseWord.runOps_prefix_accessFits q full (workspaceLimit full.length q) state count hc

private theorem offset_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat) (hoff : offset ≤ 3)
    (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (haddress : state.register .address = workspaceBase full.length q) :
    MacroSafe q full [.base (.base (.constant .index offset)), .base (.base (.add .address .address .index))] state := by
  have c := constant_safe q full .index offset state hf
    (RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by omega))
  have a := single_safe q full (.base (.base (.add .address .address .index))) _ c.full
    (by
      apply fits_update c.full
      change Fits _ (state.register .address + offset)
      rw [haddress]
      exact RawCandidateWorkspaceWordMacros.workspace_offset_fits _ _ offset hoff)
    (by trivial)
  simpa only [List.cons_append, List.nil_append] using c.append a

theorem loadCache_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoff : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset))) :
    MacroSafe q full (loadCache target offset) state := by
  let rom := rawIncidenceROM q full
  let base := runOps rom RawCandidateWorkspaceBaseRAM.program state
  have b := base_safe q full state hf
  have br : base = recovered full.length q state := base_runOps q full state
  have ba : base.register .address = workspaceBase full.length q := by rw [br]; rfl
  have o := offset_safe q full offset hoff base b.full ba
  let addressed := runOps rom [.base (.base (.constant .index offset)), .base (.base (.add .address .address .index))] base
  have ha : addressed.register .address = workspaceBase full.length q + offset := by
    simp [addressed, runOps, natExecuteOp, Op.execute, Instruction.execute, ba]
  have l := single_safe q full (.base (.base (.loadHeap target .address))) addressed o.full
    (by
      apply fits_update o.full
      change Fits _ (state.heap (addressed.register .address))
      rw [ha]
      exact hsource)
    (by
      change addressed.register .address < workspaceLimit full.length q
      rw [ha]
      exact RawCandidateWorkspaceWordMacros.workspace_offset_lt_limit _ _ offset hoff)
  simpa only [loadCache, List.cons_append, List.nil_append] using b.append (o.append l)

theorem storeCache_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoff : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state) :
    MacroSafe q full (storeCache offset) state := by
  let rom := rawIncidenceROM q full
  let base := runOps rom RawCandidateWorkspaceBaseRAM.program state
  have b := base_safe q full state hf
  have br : base = recovered full.length q state := base_runOps q full state
  have ba : base.register .address = workspaceBase full.length q := by rw [br]; rfl
  have o := offset_safe q full offset hoff base b.full ba
  let addressed := runOps rom [.base (.base (.constant .index offset)), .base (.base (.add .address .address .index))] base
  have ha : addressed.register .address = workspaceBase full.length q + offset := by
    simp [addressed, runOps, natExecuteOp, Op.execute, Instruction.execute, ba]
  have s := single_safe q full (.base (.base (.storeHeap .address .value))) addressed o.full o.full
    (by
      change addressed.register .address < workspaceLimit full.length q
      rw [ha]
      exact RawCandidateWorkspaceWordMacros.workspace_offset_lt_limit _ _ offset hoff)
  simpa only [storeCache, List.cons_append, List.nil_append] using b.append (o.append s)

theorem setCache_safe (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoff : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hv : Fits (indexWidth 16 full.length q) value) : MacroSafe q full (setCache offset value) state := by
  have c := constant_safe q full .value value state hf hv
  exact c.append (storeCache_safe q full offset hoff _ c.full)

theorem incrementCache_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoff : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset) + 1)) :
    MacroSafe q full (incrementCache offset) state := by
  let rom := rawIncidenceROM q full
  have l := loadCache_safe q full .value offset hoff state hf ((Nat.le_succ _).trans_lt hinc)
  let loaded := runOps rom (loadCache .value offset) state
  have hv : loaded.register .value = state.heap (workspaceBase full.length q + offset) := by
    dsimp only [loaded]
    rw [loadCache_runOps]
    simp [RawCandidateSerializedInputRAM.loaded]
  have c := constant_safe q full .index 1 loaded l.full
    (RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by omega))
  have a := single_safe q full (.base (.base (.add .value .value .index))) _ c.full
    (by
      apply fits_update c.full
      change Fits _ (loaded.register .value + 1)
      rw [hv]
      exact hinc)
    (by trivial)
  have s := storeCache_safe q full offset hoff _ a.full
  simpa only [incrementCache, List.append_assoc, List.cons_append, List.nil_append] using
    l.append (c.append (a.append s))

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordCache
