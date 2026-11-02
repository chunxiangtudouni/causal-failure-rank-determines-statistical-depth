module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_004
public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_Branch_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

/-- A one-step analysis allowance, evaluated on the original actual error
event. The numerical children are precisely those of the frozen119 envelope. -/
noncomputable def nextPotentialAllowance (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (cache : BudgetCache I)
    (kind : ReferenceBudgetCase) (sample : Unit × input.World) : ℝ≥0∞ :=
  Branch.goodAllowance input stage cache.errors kind cache.risk +
    (PRetRiskMassFlow.writeError input C accounting budget stage).indicator
      (fun _ => Branch.badAllowance input stage cache.errors kind cache.risk) sample

theorem nextPotential_le_allowance (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (kind : ReferenceBudgetCase) (replay : replayBudget I budget history stage.val = some cache)
    (healthy : Healthy I stage.val cache.errors) (query : rankCase I stage cache.errors = some kind)
    (sample : Unit × input.World) (entered : sample ∈ stageEntryEvent input C accounting budget stage history) :
    entryEnvelopePotential input C accounting budget (stage.val + 1) sample ≤
      nextPotentialAllowance input C accounting budget stage cache kind sample := by
  by_cases hn : stage.val + 1 < I.stageCount
  · let nextStage : I.Stage := ⟨stage.val + 1, hn⟩
    change entryEnvelopePotential input C accounting budget nextStage.val sample ≤ _
    rw [entryEnvelopePotential_at_stage]
    cases nextEntered : entryHistory input C .uncapped accounting (retainedRule input budget none) nextStage sample with
    | none => exact bot_le
    | some nextHistory =>
      obtain ⟨actual, child, actualKind, error, actualReplay, childReplay, _actualHealthy, _actualValid,
        _childHealthy, _childValid, actualQuery, update, childErrors, wrong⟩ :=
        PRetRiskMassFlow.nextEntry_cache_transition input C hretained accounting budget positive small
          stage nextStage rfl sample history nextHistory entered nextEntered
      have actualEq : actual = cache := Option.some.inj (actualReplay.symm.trans replay)
      subst actual
      have kindEq : actualKind = kind := Option.some.inj (actualQuery.symm.trans query)
      subst actualKind
      simp only [childReplay]
      have bound := Branch.childEnvelope_le_allowance input stage cache child kind error healthy query update childErrors
      cases error with
      | false =>
        have hb : observationEnvelope input (stage.val + 1) child.errors child.risk ≤
            Branch.goodAllowance input stage cache.errors kind cache.risk := bound
        exact hb.trans (le_add_of_nonneg_right bot_le)
      | true =>
        have hb : observationEnvelope input (stage.val + 1) child.errors child.risk ≤
            Branch.badAllowance input stage cache.errors kind cache.risk := bound
        unfold nextPotentialAllowance
        rw [Set.indicator_of_mem (wrong rfl)]
        exact hb.trans (le_add_of_nonneg_left bot_le)
  · rw [entryEnvelopePotential_past_end input C accounting budget (stage.val + 1) sample (Nat.le_of_not_gt hn)]
    exact bot_le

theorem lintegral_nextPotentialAllowance (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) (cache : BudgetCache I) (kind : ReferenceBudgetCase) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      nextPotentialAllowance input C accounting budget stage cache kind sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        Branch.goodAllowance input stage cache.errors kind cache.risk +
      input.seededWorldLaw (Measure.dirac ())
        (PRetRiskMassFlow.writeError input C accounting budget stage ∩ stageEntryEvent input C accounting budget stage history) *
        Branch.badAllowance input stage cache.errors kind cache.risk := by
  have errorMeasurable := PRetRiskMassFlow.measurableSet_writeError input C accounting budget stage
  unfold nextPotentialAllowance
  rw [lintegral_add_right _ (measurable_const.indicator errorMeasurable), setLIntegral_const,
    lintegral_indicator errorMeasurable, setLIntegral_const, Measure.restrict_apply errorMeasurable]
  ac_rfl

theorem lintegral_nextPotential_on_entry_le (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (kind : ReferenceBudgetCase) (replay : replayBudget I budget history stage.val = some cache)
    (healthy : Healthy I stage.val cache.errors) (query : rankCase I stage cache.errors = some kind) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      entryEnvelopePotential input C accounting budget (stage.val + 1) sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        Branch.goodAllowance input stage cache.errors kind cache.risk +
      input.seededWorldLaw (Measure.dirac ())
        (PRetRiskMassFlow.writeError input C accounting budget stage ∩ stageEntryEvent input C accounting budget stage history) *
        Branch.badAllowance input stage cache.errors kind cache.risk := by
  calc
    _ ≤ ∫⁻ sample in stageEntryEvent input C accounting budget stage history,
        nextPotentialAllowance input C accounting budget stage cache kind sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_mono' (measurableSet_stageEntryEvent input C accounting budget stage history)
      intro sample entered
      exact nextPotential_le_allowance input C hretained accounting budget positive small
        stage history cache kind replay healthy query sample entered
    _ = _ := lintegral_nextPotentialAllowance input C accounting budget stage history cache kind

end PDROC.RetainedEnvelopeRun
