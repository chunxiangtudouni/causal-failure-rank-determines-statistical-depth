module

public import PaperProofs.Structure.RawTreePreprocessingParentWord
public import PaperProofs.Structure.RawCandidateSerializedChildrenWord
public import PaperProofs.Structure.RawTreePreprocessingFooterWord

/-! Actual serialization-phase linking for the original fixed raw program.
All clocks below refer to that same program and initial raw state. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingSerializationWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawTreeSerialization
open RawTreePreprocessingNat (program)
open RawCandidateWorkspaceInit (workspaceBase candidateCount)

theorem input_slice : 1206 + 443 ≤ program.length ∧
    ∀ position < 443, program.getD (1206 + position) RawCandidateSerializedInputRAM.paddingOp =
      (RawCandidateSerializedInputRAM.programAt 1206).getD position RawCandidateSerializedInputRAM.paddingOp := by
  have h := RawCandidateTreePrefix.input_slice RawTreePreprocessingNat.tail
  rw [RawCandidateTreePrefix.inputStart_eq] at h
  exact h

theorem children_slice : 1649 + 427 ≤ program.length ∧
    ∀ position < 427, program.getD (1649 + position) RawCandidateSerializedChildrenRAM.paddingOp =
      (RawCandidateSerializedChildrenRAM.programAt 1649).getD position RawCandidateSerializedChildrenRAM.paddingOp := by
  have h := RawCandidateSerializedChildrenRun.append_slice RawTreePreprocessingNat.front RawTreeOutputFinalizeRAM.program
  rw [RawTreePreprocessingNat.children_program, RawTreePreprocessingNat.front_length, RawTreePreprocessingNat.childrenStart_eq] at h
  exact h

theorem input_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawCandidateSerializedInputWordChunks.SafePoint q full program 1206 state) :
    RawTreePreprocessingWordInterface.SafePoint q full state := by
  obtain ⟨hr, offset, hoff, hp, _ha, op, hd, hx⟩ := hs
  refine ⟨hr, 1206 + offset, by have h := input_slice.1; omega, hp, ?_⟩
  intro _
  rw [hd]
  exact hx

theorem children_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hs : RawCandidateSerializedChildrenWordChunks.SafePoint q full program 1649 state) :
    RawTreePreprocessingWordInterface.SafePoint q full state := by
  obtain ⟨hr, offset, hoff, hp, _ha, op, hd, hx⟩ := hs
  refine ⟨hr, 1649 + offset, by have h := children_slice.1; omega, hp, ?_⟩
  intro _
  rw [hd]
  exact hx

/-- Input serialization preserves the earlier actual parent cache. The
written input-payload answer is unnecessary for this next safety handoff. -/
theorem children_input_of_input_phase (q : Nat) (full : List (Finset (Fin q)))
    (before after : NatState) (entry : RawCandidateTreePrefix.ParentEntry q full before)
    (ready : RawCandidateSerializedReady.StageReady q full (5 * 1649) after)
    (frame : RawCandidateSerializedInputRAM.AboveFrame full.length q
      (RawCandidateSerializedInputLayout.prefixLength q full) before after) :
    RawCandidateSerializedChildrenRAM.InputSpec q full after := by
  have parents := RawCandidateTreePrefix.cachedParents_of_aboveFrame q full entry.parents frame
  refine ⟨ready.headers, ?_⟩
  intro child hc
  have hp := parents ⟨child, hc⟩
  have haddr : RawCandidateSerializedChildrenRAM.parentAddress full.length q child =
      RawCandidateParentRAM.parentSlot (workspaceBase full.length q) (full.length + q + 1) child := by
    unfold RawCandidateSerializedChildrenRAM.parentAddress RawCandidateParentRAM.parentSlot
      RawCandidateOrderingRAM.arraySlot candidateCount
    omega
  rw [haddr]
  exact hp.trans (RawCandidateChildrenLayout.givenTreeROM_parentWords q full child hc).symm

/-- Given the already completed input phase's actual current state, the
original child program and real footer/HALT close every remaining clock. -/
theorem finish_children_all_prefix_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hl : LaminarSchedule full) (first : Nat)
    (hprefix : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program natInitial first)
    (input : RawCandidateSerializedChildrenRAM.InputSpec q full (natRun (rawIncidenceROM q full) program first natInitial))
    (hpc : (natRun (rawIncidenceROM q full) program first natInitial).pc = 5 * 1649)
    (ha : (natRun (rawIncidenceROM q full) program first natInitial).halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) program first natInitial))
    (count : Nat) :
    PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full) (rawIncidenceROM q full) program natInitial count := by
  let state := natRun (rawIncidenceROM q full) program first natInitial
  let steps := RawCandidateSerializedChildrenRun.totalSteps q full
  have hend : Fits (indexWidth 16 full.length q) (5 * (1649 + 427)) :=
    RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide)
  have hs := RawCandidateSerializedChildrenWord.serialize_nat_safe q full hq hl program 1649 children_slice.1 children_slice.2
    state input hpc ha hf hend
  have sem := RawCandidateSerializedChildrenRun.serialize q full hq hl program 1649 children_slice.1 children_slice.2
    state input hpc ha
  have lifted : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program state steps := fun k hk => children_point q full _ (hs.1 k hk)
  have allSafe : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
      (rawIncidenceROM q full) program natInitial (first + steps) :=
    PrefixSafe.add _ _ _ _ first steps hprefix lifted
  apply RawTreePreprocessingFooterWord.finish_headers_all_prefix_safe q full hq hl (first + steps) allSafe
  · rw [natRun_add]
    exact sem.input.headers
  · rw [natRun_add]
    exact sem.pc
  · rw [natRun_add]
    exact sem.active
  · rw [natRun_add]
    exact hs.2

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingSerializationWord
