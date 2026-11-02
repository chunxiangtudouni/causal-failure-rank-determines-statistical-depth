module

public import Common.PSTR_L01_PrefixPlanner_006

/-! The SAME actual native TABLE policy/history supplies the cache model.
The complete policy's legal rule is transported only to the SAME uncapped
TABLE execution, never to the generic tie. No numerical qualification or
machine-cost promise is invented. Raw parsing/paid bit implementation remain. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRQueryRecords PSTRStatistics.TableAlignment

variable {I : Instance}

theorem actual_native_rule (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule = tableRule input available budget limit)
    (sample : Unit × input.World) (clock : Nat) :
    let state := run input C .native accounting policy.rule sample clock
    ∃ cache, tableReplay input available budget state.history = some cache ∧
      recordRuleFromCache input budget limit state.history (nativeRecords available state.history) cache =
        policy.rule () state.history := by
  dsimp only
  have legal : LegalRule input C .uncapped accounting (tableRule input available budget limit) := by
    rw [← sameRule]
    exact legalRule_uncapped_of_native input C accounting policy.rule policy.legal
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting _ legal sample clock
  obtain ⟨cache, aligned, action⟩ := actual_prefix_rule input C laminar current accounting available budget
    positive small limit _ _ _ hp
  have whole := PA17L01HistoryPrefixActual004.native_table_run_eq input C accounting available budget limit
    policy sameRule sample clock
  have history := congrArg (fun state : State I => state.history) whole
  refine ⟨cache, ?_, ?_⟩
  · rw [history]
    exact aligned.parsed
  · rw [history, sameRule]
    exact action

end PaperProofs.Common.Native.PSTRTableRecordPlanner

