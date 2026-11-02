module

public import PaperProofs.Paid.PDROC_SimulatorLaw_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- A real eventual source entry supplies the finite visible guard witness
for its complete direct draw. Never-entry is the blind stop completion. -/
theorem sourceEventualReportedDraw_guardGood_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤) :
    sourceDrawGuardGood (sourceForOptionalHistory source.rule) stage
      (sourceEventualReportedDraw P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  cases he : entryHistory input C.val .uncapped accounting source.rule stage sample with
  | none =>
    have hsample : sourceEventualStageSample P fee hfee C accounting source stage sample =
        (((sample.1, none), []), sample.2 stage) := by
      change (sourceEventualHistorySeed (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample), _) = _
      rw [he]
      rfl
    have ha : (sourceEventualReportedDraw P fee hfee C accounting source stage sample).1.2.action = .stop := by
      change (sourceDirectReportedDraw P fee hfee wrapped hm stage
        (sourceEventualStageSample P fee hfee C accounting source stage sample)).1.2.action = .stop
      rw [hsample]
      rfl
    refine ⟨Or.inr (Or.inl ha), ?_⟩
    exact sourcePostwriteGuardGood_of_halted _ _ stage _
      (sourceDrawTerminalHistory_halted stage _ _ _ (Or.inl ha))
  | some history =>
    obtain ⟨start, hc, hbefore, hhistory⟩ :=
      (entryHistory_some_iff input C.val .uncapped accounting source.rule stage sample history).mp he
    have hsample : sourceEventualStageSample P fee hfee C accounting source stage sample =
        (((sample.1, some history), history), sample.2 stage) := by
      change (sourceEventualHistorySeed (sample.1, entryHistory input C.val .uncapped accounting source.rule stage sample), _) = _
      rw [he]
      rfl
    let draw := (sourceEventualReportedDraw P fee hfee C accounting source stage sample).1.2
    have hs' : (simulatorLocalTest P fee hfee wrapped hm stage).rule.stop
        ((sample.1, some history), history) (sample.2 stage).2 ≠ ⊤ := by
      rw [hsample] at hs
      exact hs
    have hd0 := simulatorDrawAt_eq_decoder_of_finite P fee hfee wrapped hm stage
      ((((sample.1, some history), history), (sample.2 stage).2)) hs'
    have hdraw : draw = simulatorDrawDecoder P fee hfee wrapped stage
        (P.binarySymmetric.experiment.stoppedTranscript (simulatorLocalTest P fee hfee wrapped hm stage)
          ((((sample.1, some history), history), (sample.2 stage).2))) := by
      change (sourceDirectReportedDraw P fee hfee wrapped hm stage
        (sourceEventualStageSample P fee hfee C accounting source stage sample)).1.2 = _
      rw [hsample]
      rfl
    have hdw : simulatorDrawAt P fee hfee wrapped stage (sample.1, some history) history (sample.2 stage).2 = some draw :=
      hd0.trans (congrArg some hdraw.symm)
    have hdSource : simulatorDrawAt P fee hfee source.rule stage sample.1 history (sample.2 stage).2 = some draw :=
      (simulatorDrawAt_optionalHistory_some P fee hfee source.rule stage sample.1 history history (sample.2 stage).2).symm.trans hdw
    have hd : simulatorDrawAt P fee hfee source.rule stage sample.1
        (run input C.val .uncapped accounting source.rule sample start).history
          (worldTapes input sample.2 stage) = some draw :=
      (congrArg (fun entry => simulatorDrawAt P fee hfee source.rule stage sample.1 entry
        ((sample.2 stage).2 : P.experiment.Tape)) hhistory).trans hdSource
    have hg := firstEntry_sourceDrawGuardGood P fee hfee C accounting source.rule source.legal
      sample start stage ⟨hc, hbefore⟩ draw hd
    rw [hhistory] at hg
    have hcoords : (sourceEventualReportedDraw P fee hfee C accounting source stage sample).1.1 =
        ((sample.1, some history), history) := by
      change (sourceEventualStageSample P fee hfee C accounting source stage sample).1 = _
      rw [hsample]
    have hreport : sourceEventualReportedDraw P fee hfee C accounting source stage sample =
        (((((sample.1, some history), history), draw), input.truthAt sample.2 stage)) :=
      Prod.ext (Prod.ext hcoords rfl) rfl
    rw [hreport]
    exact (sourceDrawGuardGood_optionalHistory_some source.rule stage sample.1 history history draw _).mpr hg
/-- The actual original full bill implies that the source's true eventual
reported-draw law satisfies the measurable guard condition almost surely.
No source success, virtual Prefix range, RCP, or extra local ET is assumed. -/
theorem sourceEventualReportedDraw_guardGood_ae (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    ∀ᵐ record ∂simulatorSourceReportedDrawLaw P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage
        (sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage),
      sourceDrawGuardGood (sourceForOptionalHistory source.rule) stage record := by
  let input := P.input fee hfee
  let wrapped := sourceForOptionalHistory source.rule
  let hm := measurable_sourceForOptionalHistory source.rule source.measurable_rule
  let test := simulatorLocalTest P fee hfee wrapped hm stage
  let η := sourceEventualDrawSeedLaw P fee hfee C accounting source ν stage
  let stop := fun sample : ((Seed × EntryHistory P.sharedInstance) × List (VisibleEvent P.sharedInstance)) ×
      input.StageSample stage => test.rule.stop sample.1 sample.2.2
  have hstop : Measurable stop := test.measurable_stop.comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hp : MeasurableSet {sample | stop sample ≠ ⊤} := (hstop (measurableSet_singleton ⊤)).compl
  have hf := sourceEventualDraw_finiteET_of_fullBill P fee hfee C accounting source ν stage hfinite
  have hfiniteStage : ∀ᵐ sample ∂η.prod (input.stageLaw stage), stop sample ≠ ⊤ := by
    apply ae_prod_stageLaw_of_conditional input stage η _ hp
    intro truth
    exact P.binarySymmetric.experiment.expectedSamples_finite_stop η test truth (hf truth)
  have hfiniteMap : ∀ᵐ sample ∂(input.seededWorldLaw ν).map
      (sourceEventualStageSample P fee hfee C accounting source stage), stop sample ≠ ⊤ := by
    rw [sourceEventualStageSample_law]
    exact hfiniteStage
  have hactualFinite := ae_of_ae_map
    (measurable_sourceEventualStageSample P fee hfee C accounting source stage).aemeasurable hfiniteMap
  have hactual : ∀ᵐ sample ∂input.seededWorldLaw ν,
      sourceDrawGuardGood wrapped stage (sourceEventualReportedDraw P fee hfee C accounting source stage sample) := by
    filter_upwards [hactualFinite] with sample hs
    exact sourceEventualReportedDraw_guardGood_of_finite P fee hfee C accounting source stage sample hs
  have hgood : ∀ᵐ record ∂(input.seededWorldLaw ν).map
      (sourceEventualReportedDraw P fee hfee C accounting source stage), sourceDrawGuardGood wrapped stage record :=
    (ae_map_iff (measurable_sourceEventualReportedDraw P fee hfee C accounting source stage).aemeasurable
      (measurableSet_sourceDrawGuardGood wrapped hm stage)).mpr hactual
  rw [sourceEventualReportedDraw_law] at hgood
  exact hgood

end PDROC

