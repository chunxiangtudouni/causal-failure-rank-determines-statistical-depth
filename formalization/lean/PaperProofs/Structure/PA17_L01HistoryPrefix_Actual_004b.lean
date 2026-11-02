module

public import PaperProofs.Structure.PA17_L01HistoryPrefix_Actual_004a
public import PaperProofs.Structure.PA17_L01HistoryPrefix_Strategy_002f
public import PaperProofs.Common.NativeRelaxation

/-! The original TABLE native history satisfies actual AllowedSequence and
all-clock prefix facts. Same-rule native/uncapped execution equality comes
from the original legal native Policy, not from a generic-picker comparison. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PA17L01HistoryPrefixActual004

open PaperProofs.Structure.LaminarTree

variable {I : Instance}

structure ActualHistoryData (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (policy : Policy input C .native accounting Unit) : Prop where
  allowed : ∀ (sample : Unit × input.World) (clock : Nat),
    PSTRCommandPrefixes.AllowedSequence I.compatibility ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history)
  commands_prefix : ∀ (sample : Unit × input.World) {earlier later : Nat}, earlier ≤ later →
    (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample earlier).history).IsPrefix
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample later).history)

theorem native_table_run_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (limit : ReferenceObservationLimit I) (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget limit)
    (sample : Unit × input.World) (clock : Nat) :
    run input C .native accounting policy.rule sample clock =
      run input C .uncapped accounting (CompactPrice.tableRule input available budget limit) sample clock := by
  exact (run_uncapped_eq_native input C accounting policy.rule policy.legal sample clock).symm.trans
    (congrArg (fun rule : PolicyRule I Unit => run input C .uncapped accounting rule sample clock) hrule)

theorem native_table_commands_allowed (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget limit)
    (sample : Unit × input.World) (clock : Nat) :
    PSTRCommandPrefixes.AllowedSequence I.compatibility ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) := by
  rw [native_table_run_eq input C accounting available budget limit policy hrule sample clock]
  have legal : LegalRule input C .uncapped accounting (CompactPrice.tableRule input available budget limit) := by
    rw [← hrule]
    exact legalRule_uncapped_of_native input C accounting policy.rule policy.legal
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting _ legal sample clock
  exact PA17L01HistoryPrefixStrategy002.prefix_commandsAt_allowed input C hl current accounting
    available budget hb hsmall limit sample.1 _ _ hp

theorem native_table_history_data (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hb : 0 < budget) (hsmall : budget ≤ 1 / 2) (limit : ReferenceObservationLimit I)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget limit) :
    ActualHistoryData input C accounting available policy := by
  refine ⟨native_table_commands_allowed input C hl current accounting available budget hb hsmall limit policy hrule, ?_⟩
  intro sample earlier later hle
  exact policy_commands_prefix input C current.1 .native accounting policy sample hle

theorem original_choice_history_data (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent))) :
    ActualHistoryData input C accounting available policy := by
  exact native_table_history_data input C hl current accounting available budget choice.positive choice.small
    (some (referenceQuota input exponent)) policy hrule

end PaperProofs.Common.Native.PA17L01HistoryPrefixActual004
