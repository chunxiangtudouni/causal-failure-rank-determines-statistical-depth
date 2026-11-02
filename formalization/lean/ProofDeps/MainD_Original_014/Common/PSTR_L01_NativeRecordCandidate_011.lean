module

public import Common.PSTR_L01_RecordCandidatePlanner_010

/-! The eligibility-free logical candidate planner returns the SAME actual
native TABLE action/output. The omitted guard is proved nonbinding from
the actual Prefix, never assumed by the original caller. Raw Bool code,
real scalar arithmetic, quotas and total machine cost remain to construct. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRTableRecordPlanner

open PaperProofs.Statistics PaperProofs.Structure PaperProofs.Structure.LaminarTree
open CompactPrice PSTRQueryRecords

variable {I : Instance}

theorem actual_native_record_candidate (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule = tableRule input available budget limit)
    (sample : Unit × input.World) (clock : Nat) :
    let state := run input C .native accounting policy.rule sample clock
    recordCandidatePlanner input available budget limit state.history (nativeRecords available state.history) =
      policy.rule () state.history := by
  dsimp only
  rw [PA17L01HistoryPrefixActual004.native_table_run_eq input C accounting available budget limit
    policy sameRule sample clock]
  have legal : LegalRule input C .uncapped accounting (tableRule input available budget limit) := by
    rw [← sameRule]
    exact legalRule_uncapped_of_native input C accounting policy.rule policy.legal
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting _ legal sample clock
  rw [sameRule]
  exact actual_prefix_record_candidate input C laminar current accounting available budget
    positive small limit _ _ _ hp

theorem actual_native_candidate_output (input : StatisticalInput I) (C : Contract I)
    (laminar : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : Rat)
    (positive : 0 < budget) (small : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (sameRule : policy.rule = tableRule input available budget limit)
    (sample : Unit × input.World) (clock : Nat) :
    let state := run input C .native accounting policy.rule sample clock
    RationalControllerComputation.encode (RationalControllerComputation.encodeAction
      (recordCandidatePlanner input available budget limit state.history (nativeRecords available state.history))) =
      RationalControllerComputation.encode (RationalControllerComputation.encodeAction (policy.rule () state.history)) := by
  dsimp only
  rw [actual_native_record_candidate input C laminar current accounting available budget
    positive small limit policy sameRule sample clock]

end PaperProofs.Common.Native.PSTRTableRecordPlanner
