module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_002
public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_003
public import PaperProofs.Retained.PRet_RiskMassFlow_Transition_010
public import PaperProofs.Common.ReferenceGlobalCost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

theorem stageEntryEvent_eq (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) :
    stageEntryEvent input C accounting budget stage history =
      PRetRiskMassFlow.entryEvent input C accounting budget stage history := rfl

theorem entryEnvelopePotential_of_entry (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) (cache : BudgetCache I) (sample : Unit × input.World)
    (entered : sample ∈ stageEntryEvent input C accounting budget stage history)
    (replay : replayBudget I budget history stage.val = some cache) :
    entryEnvelopePotential input C accounting budget stage.val sample =
      observationEnvelope input stage.val cache.errors cache.risk := by
  change entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history at entered
  rw [entryEnvelopePotential_at_stage]
  simp only [entered, replay]

theorem entryEnvelopePotential_zero_of_no_entry (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World)
    (absent : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none) :
    entryEnvelopePotential input C accounting budget stage.val sample = 0 := by
  rw [entryEnvelopePotential_at_stage, absent]

/-- A later genuine entry cannot appear after the run has never entered
the preceding physical stage. This uses actual same-run cursor causality. -/
theorem nextPotential_zero_of_no_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ)
    (stage : I.Stage) (sample : Unit × input.World)
    (absent : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none) :
    entryEnvelopePotential input C accounting budget (stage.val + 1) sample = 0 := by
  by_cases hn : stage.val + 1 < I.stageCount
  · let nextStage : I.Stage := ⟨stage.val + 1, hn⟩
    change entryEnvelopePotential input C accounting budget nextStage.val sample = 0
    rw [entryEnvelopePotential_at_stage]
    cases entered : entryHistory input C .uncapped accounting (retainedRule input budget none) nextStage sample with
    | none => rfl
    | some history =>
      obtain ⟨clock, cursor, _first, _seen⟩ :=
        (entryHistory_some_iff input C .uncapped accounting (retainedRule input budget none) nextStage sample history).mp entered
      have before := run_cursor_lt_of_no_entry input C .uncapped accounting (retainedRule input budget none)
        (retainedRule_uncapped_legal input C hretained accounting budget none) sample stage absent clock
      rw [cursor] at before
      change stage.val + 1 < stage.val at before
      omega
  · exact entryEnvelopePotential_past_end input C accounting budget (stage.val + 1) sample (Nat.le_of_not_gt hn)

theorem lintegral_potential_on_entry (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (replay : replayBudget I budget history stage.val = some cache) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      entryEnvelopePotential input C accounting budget stage.val sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        observationEnvelope input stage.val cache.errors cache.risk := by
  calc
    _ = ∫⁻ _sample in stageEntryEvent input C accounting budget stage history,
        observationEnvelope input stage.val cache.errors cache.risk ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_stageEntryEvent input C accounting budget stage history)
      intro sample entered
      exact entryEnvelopePotential_of_entry input C accounting budget stage history cache sample entered replay
    _ = observationEnvelope input stage.val cache.errors cache.risk *
        input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) := setLIntegral_const _ _
    _ = _ := mul_comm _ _

end PDROC.RetainedEnvelopeRun
