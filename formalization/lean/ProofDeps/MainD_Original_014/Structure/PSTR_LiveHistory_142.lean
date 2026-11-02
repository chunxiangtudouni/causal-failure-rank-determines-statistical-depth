module

public import Structure.PSTR_LiveControllerScripts_140
public import Structure.PA17_L01HistoryPrefix_Actual_004b

/-! Consume the existing ACTUAL TABLE-history bridge and the actual1514-op
live program. One final count list witnesses every native clock prefix on
the SAME prepared heap. No history eligibility or callback answer is input.
This is the physical Word part, not a Bool planner/preparation cost claim. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRLiveHistory

open PaperProofs.Structure.LaminarTree
open AlgorithmClaims CompactControllerClaims PA17A19RuntimeEntry020

variable {I : Instance}

theorem actual_native_words (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (heap : BitVec (wordBits I.compatibility) → BitVec (wordBits I.compatibility))
    (rep : HeapRepresents I.toolCount I.compatibility (capacity I.compatibility)
      ⟨0, Finset.univ \ available, false⟩ heap)
    (sample : Unit × input.World) (horizon : Nat) :
    let commands := CompactPrice.commandsAt I (run input C .native accounting policy.rule sample horizon).history
    ∃ counts : List Nat,
      counts.length = commands.length ∧ commands.length ≤ 2 * I.stageCount + 1 ∧
      CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
        (allocatedWords I.compatibility) PSTRLiveControllerCode.program
        ⟨0, Finset.univ \ available, false⟩ commands counts heap ∧
      commandsCost I.toolCount I.compatibility PSTRLiveControllerCode.program commands counts heap ≤
        65536 * (I.stageCount + 1) * liveWork I.toolCount (treeSize I.toolCount I.compatibility) ∧
      ∀ clock : Fin horizon,
        let history := (run input C .native accounting policy.rule sample clock.val).history
        let prefixCommands := CompactPrice.commandsAt I history
        let records := CompactPrice.queryRecords I.toolCount I.compatibility PSTRLiveControllerCode.program
          prefixCommands (counts.take prefixCommands.length) heap
        prefixCommands.IsPrefix commands ∧
        CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
          (allocatedWords I.compatibility) PSTRLiveControllerCode.program
          ⟨0, Finset.univ \ available, false⟩ prefixCommands (counts.take prefixCommands.length) heap ∧
        records.length ≤ 4 * (2 * I.stageCount + 1) ∧
        ∀ word ∈ records, word < 2 ^ wordBits I.compatibility := by
  let commands := CompactPrice.commandsAt I (run input C .native accounting policy.rule sample horizon).history
  have actual := PA17L01HistoryPrefixActual004.original_choice_history_data input C hl current
    accounting available delta budget exponent choice policy hrule
  have length : commands.length ≤ 2 * I.stageCount + 1 :=
    PSTRStatistics.CompactABI.commandsAt_length_le _
  obtain ⟨counts, countsLength, execution, cost, prefixes⟩ :=
    PSTRLiveController.actual_bounded_prefixes I.compatibility hl ⟨0, Finset.univ \ available, false⟩
      commands (actual.allowed sample horizon) length heap rep
  refine ⟨counts, countsLength, length, execution, cost, ?_⟩
  intro clock
  have prefixCommands := actual.commands_prefix sample (Nat.le_of_lt clock.isLt)
  refine ⟨prefixCommands, prefixes _ prefixCommands, ?_, ?_⟩
  · exact PSTRStatistics.CompactABI.actualQueryRecords_length_le _ _ _ _
  · exact PSTRStatistics.CompactABI.queryRecords_wordBound I.compatibility _ _ _ _

end PaperProofs.Common.Native.PSTRLiveHistory
