module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009am

/-! Concrete fixed281op parent/init/descent control composition. Only the
same-call header's encoded-node bound is an internal entry fact; all local
scratch, candidate bounds, fuel and exported tool0 are produced by code. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure CoreEmbedded (bits origin : Nat) (containing : List PackingOp) : Prop where
  bound : origin + (selectionCoreAt origin).length ≤ containing.length
  code : ∀ i (hi : i < (selectionCoreAt origin).length),
    containing[origin + i]'(by omega) = (selectionCoreAt origin)[i]
  words : WordsFit bits (packingCode containing)
  pcfit : Fits bits (5 * containing.length)

theorem core_phase_code {bits origin : Nat} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (before block after : List PackingOp) (heq : selectionCoreAt origin = before ++ block ++ after) :
    ∀ i (hi : i < block.length), containing[(origin + before.length) + i]'(by
      have hl := congrArg List.length heq
      have hb := em.bound
      simp only [List.length_append] at hl
      omega) = block[i] := by
  intro i hi
  have hl := congrArg List.length heq
  simp only [List.length_append] at hl
  have hc := em.code (before.length + i) (by omega)
  have hm : (selectionCoreAt origin)[before.length + i]'(by omega) = block[i] := by
    simpa only [heq] using PA17A19RuntimeRanks008.middle_get before block after i hi
  simpa only [Nat.add_assoc] using hc.trans hm

theorem core_parent_embedded {bits origin : Nat} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing) : ParentEmbedded bits origin containing := by
  refine ⟨by have hh := em.bound; rw [selectionCoreAt_length, parentProgramAt_length] at *; omega, ?_, em.words, em.pcfit⟩
  have he : selectionCoreAt origin = [] ++ parentProgramAt origin ++ (descendInit ++ descendProgramAt (origin + 190)) := by
    simp only [selectionCoreAt, List.nil_append, List.append_assoc]
  simpa only [List.length_nil, Nat.add_zero] using core_phase_code em [] (parentProgramAt origin) _ he

theorem core_init_code {bits origin : Nat} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing) :
    ∀ i (hi : i < descendInit.length), containing[(origin + 164) + i]'(by
      have hh := em.bound; rw [selectionCoreAt_length] at hh; rw [descendInit_length] at hi; omega) = descendInit[i] := by
  have he : selectionCoreAt origin = parentProgramAt origin ++ descendInit ++ descendProgramAt (origin + 190) := rfl
  simpa only [parentProgramAt_length] using core_phase_code em (parentProgramAt origin) descendInit _ he

theorem core_desc_embedded {bits origin : Nat} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing) : DescEmbedded bits (origin + 190) containing := by
  refine ⟨by have hh := em.bound; rw [selectionCoreAt_length, descendProgramAt_length] at *; omega, ?_, em.words, em.pcfit⟩
  have he : selectionCoreAt origin = (parentProgramAt origin ++ descendInit) ++ descendProgramAt (origin + 190) ++ [] := by
    simp only [selectionCoreAt, List.append_nil]
  simpa only [List.length_append, parentProgramAt_length, descendInit_length] using
    core_phase_code em (parentProgramAt origin ++ descendInit) (descendProgramAt (origin + 190)) [] he

theorem fetched_core_init {bits origin : Nat} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing) (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 164))) (ha : state.halted = false) :
    packingRun rom containing 26 state = executeOps rom descendInit state := by
  simpa only [descendInit_length] using straight_segment rom containing descendInit (origin + 164)
    (by have hh := em.bound; rw [selectionCoreAt_length, descendInit_length] at *; omega)
    (core_init_code em) descendInit_straight em.words em.pcfit state hp ha

def coreSteps (size : Nat) : Nat := parentSteps size + 26 + descendSteps size

theorem coreSteps_eq (size : Nat) : coreSteps size = 203 * size + 97 := by
  unfold coreSteps descendSteps
  rw [parentSteps_eq]
  omega

theorem actual_core_kernel {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : CoreEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size) :
    let after := packingRun (callInput q full command) containing (coreSteps size) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 281)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits 0 ∧
      ReverseHeapData full configuration capWords header base counts parents size after.heap ∧
      CandidateBounded header q size after.heap ∧
      after.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size) ∧
      after.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size) := by
  let rom := callInput q full command
  let parented := packingRun rom containing (parentSteps size) state
  let initialized := packingRun rom containing 26 parented
  have hp := actual_parent_kernel (core_parent_embedded em) layout command configuration row budget state
    data.represents data.width data.mask data.parentBound data.counts_eq data.parents_eq data.base_eq data.budgetBound
    data.rowWord data.selectedWord data.address data.pc data.active
  have hc := actual_parent_candidateBounded (core_parent_embedded em) layout command configuration state data
  have hn : (parented.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size := by
    rw [actual_parent_frame (core_parent_embedded em) layout command configuration state data (parentSteps size) le_rfl
      (header + 1) (layout.headerFits 1 (by decide)) (.inl (by omega))]
    exact hnode
  have hi := execute_desc_initial_ready layout command configuration parented hp.2.2.2.2 hc hn hp.2.2.1 hp.2.1 hp.1
  have hr : DescReady full configuration (origin + 190) capWords header base counts parents size size initialized := by
    dsimp only [initialized]
    rw [fetched_core_init em rom parented hp.2.1 hp.1]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hi.1
  have hd := actual_desc_loop (core_desc_embedded em) layout command configuration initialized hr
  dsimp only
  rw [coreSteps, run_add, run_add]
  exact ⟨hd.1, by simpa only [Nat.add_assoc, Nat.reduceAdd] using hd.2.1,
    hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, hd.2.2.2.2.2.1, hd.2.2.2.2.2.2.1, hd.2.2.2.2.2.2.2⟩

theorem actual_core_trace {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (coreSteps size) state).length ≤ 3600 * (size + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (coreSteps size) state
  rw [coreSteps_eq] at hh ⊢
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
