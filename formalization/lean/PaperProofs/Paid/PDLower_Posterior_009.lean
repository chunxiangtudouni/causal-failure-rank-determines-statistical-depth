module

public import PaperProofs.Paid.PDLower_Posterior_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem markedPosteriorComparison (P : Parameters) : P.MarkedPosteriorComparison.{u} := by
  intro fee hf C mode accounting Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy
  let source := PDROC.uncappedSourcePolicy (P.input fee hf) C.val mode accounting policy
  have hr : run (P.input fee hf) C.val .uncapped accounting source.rule =
      run (P.input fee hf) C.val mode accounting policy.rule := by
    funext sample n
    exact PDROC.uncappedSourcePolicy_run (P.input fee hf) C.val mode accounting policy sample n
  have he (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hf).World) :
      entryHistory (P.input fee hf) C.val .uncapped accounting source.rule stage sample =
      entryHistory (P.input fee hf) C.val mode accounting policy.rule stage sample := by
    cases he : entryHistory (P.input fee hf) C.val mode accounting policy.rule stage sample with
    | none =>
      apply (entryHistory_none_iff _ _ _ _ _ _ _).mpr
      intro hn
      apply (entryHistory_none_iff _ _ _ _ _ _ _).mp he
      simpa only [hr] using hn
    | some history =>
      apply (entryHistory_some_iff _ _ _ _ _ _ _ _).mpr
      simpa only [hr] using (entryHistory_some_iff _ _ _ _ _ _ _ _).mp he
  have hs (stage : P.sharedInstance.Stage) :
      P.survivingEntry fee hf C .uncapped accounting source.rule stage =
        P.survivingEntry fee hf C mode accounting policy.rule stage := by
    ext sample
    simp only [Parameters.survivingEntry, Parameters.actualSurvivingEntry,
      Parameters.nextStageFilledEntry, he, hr]
  have hc (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.paidRunReviewCount fee hf C .uncapped accounting source.rule sample stage =
      P.paidRunReviewCount fee hf C mode accounting policy.rule sample stage := by
    unfold Parameters.paidRunReviewCount
    simp only [hr]
  have hp (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage =
      P.paidRunPosteriorError fee hf C mode accounting policy.rule sample stage := by
    exact congrArg (fun count : ℕ∞ => if count = 0 then (1 / 2 : ℝ) else if count = ⊤ then 0 else
      P.binarySymmetric.wordPosteriorError ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩) (hc sample stage)
  have hd (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.actualOrdinaryDecision fee hf C .uncapped accounting source.rule sample stage =
      P.actualOrdinaryDecision fee hf C mode accounting policy.rule sample stage := by
    classical
    exact congrArg (fun running : Seed × (P.input fee hf).World → ℕ → State P.sharedInstance =>
      if ∃ n : ℕ, (running sample n).ledger.written stage = some true then some true
      else if ∃ n : ℕ, (running sample n).ledger.written stage = some false then some false else none) hr
  have hfilled (sample : Seed × (P.input fee hf).World) (stage : P.sharedInstance.Stage) :
      P.filledOrdinaryDecision fee hf C .uncapped accounting source.rule sample stage =
      P.filledOrdinaryDecision fee hf C mode accounting policy.rule sample stage := by
    unfold Parameters.filledOrdinaryDecision
    rw [hd sample stage]
    cases hd' : P.actualOrdinaryDecision fee hf C mode accounting policy.rule sample stage with
    | some bit => rfl
    | none =>
      exact congrArg (fun count : ℕ∞ => if count = ⊤ then false else
        P.experiment.posteriorRecordDecision ((), ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩)) (hc sample stage)
  have hm (stage : P.sharedInstance.Stage) :
      P.markedErrorEvent fee hf C .uncapped accounting source.rule stage =
      P.markedErrorEvent fee hf C mode accounting policy.rule stage := by
    ext sample
    change (sample ∈ P.survivingEntry fee hf C .uncapped accounting source.rule stage ∧
      P.filledOrdinaryDecision fee hf C .uncapped accounting source.rule sample stage ≠ (sample.2 stage).1) ↔
      (sample ∈ P.survivingEntry fee hf C mode accounting policy.rule stage ∧
        P.filledOrdinaryDecision fee hf C mode accounting policy.rule sample stage ≠ (sample.2 stage).1)
    rw [hs stage, hfilled sample stage]
  have h : (∑ stage : P.sharedInstance.Stage,
      ∫⁻ sample, (P.survivingEntry fee hf C .uncapped accounting source.rule stage).indicator
        (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C .uncapped accounting source.rule sample stage)) sample
          ∂(P.input fee hf).seededWorldLaw ν) ≤
      ∑ stage : P.sharedInstance.Stage, (P.input fee hf).seededWorldLaw ν
        (P.markedErrorEvent fee hf C .uncapped accounting source.rule stage) := by
    apply Finset.sum_le_sum
    intro stage _
    exact markedPosterior_stage_lower_uncapped P fee hf C accounting source ν stage
  simpa only [hs, hp, hm] using h

theorem posteriorFailureAllowance (P : Parameters) : P.PosteriorFailureAllowance.{u} := by
  intro fee hf C mode accounting Seed m
  let : MeasurableSpace Seed := m
  intro ν hν
  let : IsProbabilityMeasure ν := hν
  intro policy hrisk
  have hp := (markedPosteriorComparison P) fee hf C mode accounting Seed m ν hν policy
  have hm := (markedFailureAllowance P) fee hf C mode accounting Seed m ν hν policy
  exact hp.trans (hm.2 hrisk)

theorem oneFailureAllowance (P : Parameters) : P.OneFailureAllowance.{u} :=
  ⟨markedPosteriorComparison P, markedFailureAllowance P, posteriorFailureAllowance P⟩

end PDLower
