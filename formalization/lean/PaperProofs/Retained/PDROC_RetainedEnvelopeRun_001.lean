module

public import PaperProofs.Retained.PRet_RiskMassFlow_Realization_005
public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

def stageEntryEvent (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) (history : List (VisibleEvent I)) : Set (Unit × input.World) :=
  {sample | entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history}

/-- The original entry-selected posterior stopping time; missing entries
and the actual non-testing branch contribute no observation allowance. -/
noncomputable def entrySampleBound (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) : ℕ∞ :=
  match entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
  | none => 0
  | some history => match PRetRiskMassFlow.entryTarget I budget stage history with
    | none => 0
    | some p => (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2

private theorem reportedWrite_reviews (C : Contract I) (state : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C state stage bit).reviews = state.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem prefix_reviews_le_entrySampleBound (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (sample : Unit × input.World) {n : ℕ} {state : State I}
    (path : Prefix input C .uncapped accounting (retainedRule input budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n state) :
    ∀ stage : I.Stage, state.ledger.reviews stage ≤ entrySampleBound input C accounting budget stage sample := by
  induction path with
  | initial => intro stage; exact bot_le
  | @next n state next earlier step ih =>
    generalize action : retainedRule input budget none sample.1 state.history = selected at step
    cases step with
    | review current live port resources =>
      intro stage
      by_cases same : stage = current
      · subst stage
        obtain ⟨history, p, entry, target, strict⟩ := PRetRiskMassFlow.prefix_review_realization
          input C hretained accounting budget positive small sample earlier live.1 current action
        simp only [record, reviewLedger, Function.update_self, entrySampleBound, entry, target]
        have finite := prefix_reviews_natCast_toNat input C .uncapped accounting (retainedRule input budget none)
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier current
        have bound : ((state.ledger.reviews current).toNat : ℕ∞) <
            (input.experiment current).posteriorThresholdStop p (sample.2 current).2 := by
          rw [finite]
          exact strict
        simpa only [Nat.cast_add, Nat.cast_one, finite] using
          PRetRiskMassFlow.natCast_succ_le_of_lt (state.ledger.reviews current).toNat _ bound
      · simpa only [record, reviewLedger, Function.update_of_ne same] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

theorem stageObservationBill_le_entryCharge (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Unit × input.World) :
    runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample ≤
      (input.experiment stage).observationCharge (entrySampleBound input C accounting budget stage sample) := by
  rw [input.observationCharge_agrees]
  apply iSup_le
  intro clock
  obtain ⟨_, _, path⟩ := run_has_prefix input C .uncapped accounting (retainedRule input budget none)
    (retainedRule_uncapped_legal input C hretained accounting budget none) sample clock
  exact mul_le_mul_right (ENat.toENNReal_mono (prefix_reviews_le_entrySampleBound input C hretained accounting
    budget positive small sample path stage)) _

theorem stageObservationBill_zero_of_no_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (sample : Unit × input.World)
    (absent : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none) :
    runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample = 0 := by
  have bound := stageObservationBill_le_entryCharge input C hretained accounting budget positive small stage sample
  have zero : runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample ≤ (0 : ℝ≥0∞) := by
    simpa only [entrySampleBound, absent, BinaryExperiment.observationCharge_zero] using bound
  exact le_antisymm zero (show (0 : ℝ≥0∞) ≤ _ from bot_le)

theorem stageObservationBill_zero_of_entry_none (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (sample : Unit × input.World)
    (entry : sample ∈ stageEntryEvent input C accounting budget stage history)
    (target : PRetRiskMassFlow.entryTarget I budget stage history = none) :
    runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample = 0 := by
  have bound := stageObservationBill_le_entryCharge input C hretained accounting budget positive small stage sample
  change entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history at entry
  have zero : runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample ≤ (0 : ℝ≥0∞) := by
    simpa only [entrySampleBound, entry, target, BinaryExperiment.observationCharge_zero] using bound
  exact le_antisymm zero (show (0 : ℝ≥0∞) ≤ _ from bot_le)

end PDROC.RetainedEnvelopeRun
