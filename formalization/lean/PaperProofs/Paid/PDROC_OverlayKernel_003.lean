module

public import PaperProofs.Paid.PDROC_OverlayKernel_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem auxiliaryRecord_posteriorMass_oppositeDecision (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) :
    P.binarySymmetric.wordPosteriorMass (!(record.decision.getD record.orientation))
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ =
        P.recordDecisionError record := by
  by_cases hd : record.decision.getD record.orientation = record.orientation
  · simpa only [PaperProofs.Paid.Parameters.recordDecisionError, hd, ↓reduceIte] using
      auxiliaryRecord_posteriorMass_opposite P record
  · have hn : (!(record.decision.getD record.orientation)) = record.orientation := by
      cases h1 : record.decision.getD record.orientation <;>
        cases h2 : record.orientation <;> simp_all
    rw [hn, auxiliaryRecord_posteriorMass_oriented]
    simp only [PaperProofs.Paid.Parameters.recordDecisionError, hd, ↓reduceIte]

theorem auxiliaryRecord_posteriorMass_decision (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) :
    P.binarySymmetric.wordPosteriorMass (record.decision.getD record.orientation)
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ =
        1 - P.recordDecisionError record := by
  have hsum := P.binarySymmetric.wordPosteriorMass_sum
    ⟨record.observations.length, fun k => record.observations[k.val]⟩
  have ho := auxiliaryRecord_posteriorMass_oppositeDecision P record
  cases hd : record.decision.getD record.orientation <;>
    simp only [hd, Bool.not_true, Bool.not_false] at ho ⊢ <;> linarith

/-- The truth coordinate is reconstructed from the genuine current report.
It is an output of the local experiment, never a private-seed coordinate. -/
noncomputable def overlayLocalVirtualTruth (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (truth : Bool)
    (sample : (((Bool × Bool) × P.experiment.Tape) × Bool)) : Bool :=
  Bool.xor (record.decision.getD record.orientation)
    (((P.overlayRecordTest fee hfee record).rule.decision sample.1.1 sample.1.2 != truth) || sample.2)

theorem measurable_overlayLocalVirtualTruth (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (record : AuxiliaryRecord) (truth : Bool) :
    Measurable (overlayLocalVirtualTruth P fee hfee record truth) :=
  (measurable_of_countable (fun pair : Bool × Bool =>
    Bool.xor (record.decision.getD record.orientation) ((pair.1 != truth) || pair.2))).comp
      (((P.overlayRecordTest fee hfee record).measurable_decision.comp measurable_fst).prodMk measurable_snd)

theorem overlayLocal_virtualTruth_error_probability (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (record : AuxiliaryRecord) (truth : Bool) :
    overlayLocalExperimentLaw P fee hfee record truth
      {sample | overlayLocalVirtualTruth P fee hfee record truth sample ≠
        record.decision.getD record.orientation} = ENNReal.ofReal (P.recordDecisionError record) := by
  have hset : {sample | overlayLocalVirtualTruth P fee hfee record truth sample ≠
        record.decision.getD record.orientation} =
      overlayKernelVirtualEvent (overlayLocalErrorEvent P fee hfee record truth) := by
    ext sample
    cases hd : record.decision.getD record.orientation <;>
      cases hg : (P.overlayRecordTest fee hfee record).rule.decision sample.1.1 sample.1.2 <;>
      cases truth <;> cases hm : sample.2 <;>
      simp [overlayLocalVirtualTruth, overlayKernelVirtualEvent, overlayLocalErrorEvent, hd, hg, hm]
  rw [hset]
  exact overlayLocal_virtual_probability P fee hfee record truth

/-- Full Boolean posterior kernel, for each actual truth. Thus it can be
integrated against arbitrary old-seed/full-entry gates without revealing
the current latent truth or conditioning on the fresh mixture/FP coins. -/
theorem overlayLocal_virtualTruth_singleton_probability (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (record : AuxiliaryRecord) (truth virtualTruth : Bool) :
    overlayLocalExperimentLaw P fee hfee record truth
      {sample | overlayLocalVirtualTruth P fee hfee record truth sample = virtualTruth} =
        ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass virtualTruth
          ⟨record.observations.length, fun k => record.observations[k.val]⟩) := by
  let d := record.decision.getD record.orientation
  by_cases hd : virtualTruth = d
  · subst virtualTruth
    rw [auxiliaryRecord_posteriorMass_decision]
    have hset : {sample | overlayLocalVirtualTruth P fee hfee record truth sample = d} =
        {sample | overlayLocalVirtualTruth P fee hfee record truth sample ≠ d}ᶜ := by
      ext sample
      simp
    have hm : MeasurableSet {sample | overlayLocalVirtualTruth P fee hfee record truth sample ≠ d} :=
      ((measurable_overlayLocalVirtualTruth P fee hfee record truth) (measurableSet_singleton d)).compl
    let : IsProbabilityMeasure (overlayLocalExperimentLaw P fee hfee record truth) := by
      unfold overlayLocalExperimentLaw
      infer_instance
    have he0 : 0 ≤ P.recordDecisionError record :=
      (P.recordPosteriorError_pos record).le.trans (P.recordDecisionError_bounds record).1
    rw [hset, measure_compl hm (measure_ne_top _ _), measure_univ,
      overlayLocal_virtualTruth_error_probability,
      ENNReal.ofReal_sub 1 he0]
    norm_num
  · have hn : virtualTruth = !d := by
      cases virtualTruth <;> cases hd' : d <;> simp_all
    rw [hn, auxiliaryRecord_posteriorMass_oppositeDecision]
    have hset : {sample | overlayLocalVirtualTruth P fee hfee record truth sample = !d} =
        {sample | overlayLocalVirtualTruth P fee hfee record truth sample ≠ d} := by
      ext sample
      cases overlayLocalVirtualTruth P fee hfee record truth sample <;> cases d <;> simp
    rw [hset]
    exact overlayLocal_virtualTruth_error_probability P fee hfee record truth

end PDROC
