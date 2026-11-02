module

public import Structure.PSTR_StageQueryRecords_144

/-! Actual TABLE histories discharge the completed-stage transition facts.
The resulting record list is a theorem about actual physical query output;
it never becomes a new rank-answer input to the original caller. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRQueryRecords

open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PA17L01HistoryPrefixCommands001 PA17L01HistoryPrefixStrategy002

variable {I : Instance}

noncomputable def nativeRecords (available : Finset I.Tool) (history : List (VisibleEvent I)) : List Nat :=
  let count := min (historyCursor history) I.stageCount
  stageRecords I.compatibility (stageUsed available history) 0 count ++
    if historyCursor history < I.stageCount then
      stageWords I.compatibility (stageUsed available history) count else []

theorem native_stageTransitions (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (sample : Unit × input.World) (clock : Nat) :
    let history := (run input C .native accounting policy.rule sample clock).history
    StageTransitions I.compatibility (declarationAt history) (stageUsed available history)
      (min (historyCursor history) I.stageCount) := by
  rw [PA17L01HistoryPrefixActual004.native_table_run_eq input C accounting available budget
    (some (referenceQuota input exponent)) policy hrule sample clock]
  have legal : LegalRule input C .uncapped accounting
      (CompactPrice.tableRule input available budget (some (referenceQuota input exponent))) := by
    rw [← hrule]
    exact legalRule_uncapped_of_native input C accounting policy.rule policy.legal
  obtain ⟨_, _, prefixRun⟩ := run_has_prefix input C .uncapped accounting _ legal sample clock
  exact prefix_stageTransitions input C hl current accounting available budget choice.positive choice.small
    (some (referenceQuota input exponent)) sample.1 _ _ prefixRun

theorem history_semantic_records (available : Finset I.Tool) (history : List (VisibleEvent I))
    (transitions : StageTransitions I.compatibility (declarationAt history) (stageUsed available history)
      (min (historyCursor history) I.stageCount))
    (allowed : PSTRCommandPrefixes.AllowedSequence I.compatibility ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I history)) :
    semanticRecords I.compatibility ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I history) allowed = nativeRecords available history := by
  let count := min (historyCursor history) I.stageCount
  have hcount : count ≤ I.compatibility.length := Nat.min_le_right _ _
  have zero : stageConfiguration (stageUsed available history) 0 =
      (⟨0, Finset.univ \ available, false⟩ : Configuration I.toolCount) := by
    unfold stageConfiguration
    rw [stageUsed_zero]
  have allowedStage : PSTRCommandPrefixes.AllowedSequence I.compatibility
      (stageConfiguration (stageUsed available history) 0) (CompactPrice.commandsAt I history) :=
    zero.symm ▸ allowed
  refine (semanticRecords_congr I.compatibility _ _ _ _ zero.symm rfl allowed allowedStage).trans ?_
  by_cases current : historyCursor history < I.stageCount
  · have commandsEq := commandsAt_eq_pairs history
    rw [ite_eq_left current] at commandsEq
    have allowedPairs : PSTRCommandPrefixes.AllowedSequence I.compatibility
        (stageConfiguration (stageUsed available history) 0)
        (pairCommands (declarationAt history) 0 count ++ if true then [.query] else []) :=
      commandsEq ▸ allowedStage
    refine (semanticRecords_congr I.compatibility _ _ _ _ rfl commandsEq allowedStage allowedPairs).trans ?_
    have exactRecords := pair_extra_records I.compatibility (declarationAt history)
      (stageUsed available history) count hcount transitions 0 count (by omega) true allowedPairs
    dsimp only [nativeRecords]
    rw [ite_eq_left current]
    simpa only [Nat.zero_add, ite_true] using exactRecords
  · have commandsEq := commandsAt_eq_pairs history
    rw [ite_eq_right current] at commandsEq
    have allowedPairs : PSTRCommandPrefixes.AllowedSequence I.compatibility
        (stageConfiguration (stageUsed available history) 0)
        (pairCommands (declarationAt history) 0 count ++ if false then [.query] else []) :=
      commandsEq ▸ allowedStage
    refine (semanticRecords_congr I.compatibility _ _ _ _ rfl commandsEq allowedStage allowedPairs).trans ?_
    have exactRecords := pair_extra_records I.compatibility (declarationAt history)
      (stageUsed available history) count hcount transitions 0 count (by omega) false allowedPairs
    dsimp only [nativeRecords]
    rw [ite_eq_right current]
    simpa only [Nat.zero_add, Bool.false_eq_true, ite_false] using exactRecords

theorem actual_native_records {bits constant capWords heapWords : Nat}
    (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (program : List PackingOp) (sample : Unit × input.World) (clock : Nat)
    (counts : List Nat) (heap : BitVec bits → BitVec bits)
    (execution : CommandsRunClaims constant I.toolCount I.compatibility capWords heapWords program
      ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) counts heap) :
    CompactPrice.queryRecords I.toolCount I.compatibility program
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) counts heap =
      nativeRecords available (run input C .native accounting policy.rule sample clock).history := by
  exact (records_of_run I.compatibility program _ _ counts heap execution).trans
    (history_semantic_records available _
      (native_stageTransitions input C hl current accounting available delta budget exponent choice policy hrule sample clock) _)

end PaperProofs.Common.Native.PSTRQueryRecords
