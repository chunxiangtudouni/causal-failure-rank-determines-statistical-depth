module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_001
public import PaperProofs.Retained.PDROC_RetainedEnvelope_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open PaperProofs.Retained.PRetObservationEnvelope119
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

/-- The original numerical allowance evaluated at the actual full-history
entry cache. Missing entries and indices past the last physical stage are zero. -/
noncomputable def entryEnvelopePotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (next : ℕ) (sample : Unit × input.World) : ℝ≥0∞ :=
  if h : next < I.stageCount then
    match entryHistory input C .uncapped accounting (retainedRule input budget none) ⟨next, h⟩ sample with
    | none => 0
    | some history => match replayBudget I budget history next with
      | none => 0
      | some cache => observationEnvelope input next cache.errors cache.risk
  else 0

theorem entryEnvelopePotential_at_stage (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) :
    entryEnvelopePotential input C accounting budget stage.val sample =
      match entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
      | none => 0
      | some history => match replayBudget I budget history stage.val with
        | none => 0
        | some cache => observationEnvelope input stage.val cache.errors cache.risk := by
  have hs : stage.val < I.stageCount := stage.isLt
  unfold entryEnvelopePotential
  rw [dite_eq_left hs]

theorem entryEnvelopePotential_past_end (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (next : ℕ) (sample : Unit × input.World)
    (hn : I.stageCount ≤ next) : entryEnvelopePotential input C accounting budget next sample = 0 := by
  unfold entryEnvelopePotential
  exact dite_eq_right (Nat.not_lt_of_ge hn)

theorem measurable_entryEnvelopePotential (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (next : ℕ) :
    Measurable (entryEnvelopePotential input C accounting budget next) := by
  by_cases hn : next < I.stageCount
  · let price : EntryHistory I → ℝ≥0∞ := fun entry => match entry with
      | none => 0
      | some history => match replayBudget I budget history next with
        | none => 0
        | some cache => observationEnvelope input next cache.errors cache.risk
    have hm := (measurable_of_countable price).comp
      (measurable_entryHistory input C .uncapped accounting (retainedRule input budget none)
        (measurable_of_countable _) ⟨next, hn⟩)
    have he : entryEnvelopePotential input C accounting budget next =
        price ∘ entryHistory input C .uncapped accounting (retainedRule input budget none) ⟨next, hn⟩ := by
      funext sample
      exact dite_eq_left hn
    rw [he]
    exact hm
  · have he : entryEnvelopePotential input C accounting budget next = fun _ => 0 := by
      funext sample
      exact entryEnvelopePotential_past_end input C accounting budget next sample (Nat.le_of_not_gt hn)
    rw [he]
    exact measurable_const

theorem entryEnvelopePotential_initial (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (sample : Unit × input.World) :
    entryEnvelopePotential input C accounting budget 0 sample = observationEnvelope input 0 ∅ (budget / 2) := by
  by_cases hn : 0 < I.stageCount
  · let stage : I.Stage := ⟨0, hn⟩
    have entered : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some [] :=
      entryHistory_stageZero input C .uncapped accounting (retainedRule input budget none) stage rfl sample
    change entryEnvelopePotential input C accounting budget stage.val sample = _
    rw [entryEnvelopePotential_at_stage, entered]
    rfl
  · have hend : I.stageCount ≤ 0 := Nat.le_of_not_gt hn
    rw [entryEnvelopePotential_past_end input C accounting budget 0 sample hend]
    exact (observationEnvelope_past_end input 0 ∅ (budget / 2) hend).symm

theorem expected_entryEnvelopePotential_initial (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) :
    (∫⁻ sample, entryEnvelopePotential input C accounting budget 0 sample
      ∂input.seededWorldLaw (Measure.dirac ())) = observationEnvelope input 0 ∅ (budget / 2) := by
  calc
    _ = ∫⁻ _sample : Unit × input.World, observationEnvelope input 0 ∅ (budget / 2)
        ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_congr (entryEnvelopePotential_initial input C accounting budget)
    _ = _ := by simp

end PDROC.RetainedEnvelopeRun
