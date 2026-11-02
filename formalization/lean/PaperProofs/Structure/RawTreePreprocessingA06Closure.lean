module

public import PaperProofs.Structure.RawTreePreprocessingSerializationWord
public import PaperProofs.Structure.RawCandidateSerializedInputWord

/-! Original A06 closure: every phase is the same fixed raw-input program.
No unproved prefix, table, tree answer, safe-run or implementation premise
is added to the original input quantifiers. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingA06Closure

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawTreePreprocessingNat (program)
open RawTreePreprocessingSerializationWord

theorem all_prefix_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (count : Nat) :
    PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full) (rawIncidenceROM q full) program natInitial count := by
  by_cases hl : LaminarSchedule full
  · obtain ⟨first, _bound, hparentSafe, entry, _word⟩ := RawTreePreprocessingParentWord.parent_entry q full hq hl
    let before := natRun (rawIncidenceROM q full) program first natInitial
    have hpc : before.pc = 5 * 1206 := by
      simpa only [RawCandidateTreePrefix.inputStart_eq] using entry.entry.pc
    have hend : Fits (indexWidth 16 full.length q) (5 * (1206 + 443)) :=
      RawTreePreprocessingCodeBounds.constant_fits _ _ _ (by decide)
    obtain ⟨steps, _stepsBound, hsafe, hfit, ready, _written, frame⟩ :=
      RawCandidateSerializedInputWord.materialize_serialized_prefix_nat_safe q full program 1206
        input_slice.1 input_slice.2 before entry.entry.input hpc entry.entry.active entry.fit hend hq hl
    let after := natRun (rawIncidenceROM q full) program steps before
    have next : RawCandidateSerializedChildrenRAM.InputSpec q full after :=
      children_input_of_input_phase q full before after entry.entry ready frame
    have lifted : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
        (rawIncidenceROM q full) program before steps := fun k hk => input_point q full _ (hsafe k hk)
    have allSafe : PrefixSafe (RawTreePreprocessingWordInterface.SafePoint q full)
        (rawIncidenceROM q full) program natInitial (first + steps) :=
      PrefixSafe.add _ _ _ _ first steps hparentSafe lifted
    apply finish_children_all_prefix_safe q full hq hl (first + steps) allSafe
    · rw [natRun_add]
      exact next
    · rw [natRun_add]
      exact ready.pc
    · rw [natRun_add]
      exact ready.active
    · rw [natRun_add]
      exact hfit
  · exact RawTreePreprocessingFooterWord.rejects_all_prefix_safe q full hl count

theorem prefixSafety : RawTreePreprocessingWordInterface.PrefixSafety := by
  intro q full hq
  exact all_prefix_safe q full hq (16384 * treeWork full.length q)

theorem fullClaims : FullClaims :=
  RawTreePreprocessingWordInterface.fullClaims_of_prefixSafety prefixSafety

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingA06Closure
