module

public import PaperProofs.Common.NativePreReportBoundary
public import PaperProofs.Star.LatePosterior
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Complete C04 normalization of the ACTUAL native pre-report record.
No conditional-probability kernel, finite-ET, MAP or success restriction is
introduced. Arbitrary private-seed universes and measurable record events
are handled by seed rectangles and the countable public-history partition. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Star.Parameters

open Common Common.Native Statistics

universe u

def ValidCutHistory (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) : Prop :=
  ∀ i symbol, symbol ∈ historyObservations history i → symbol < P.channel.experiment.alphabetSize

private theorem emptyWord_of_length_zero (E : BinaryExperiment) (word : E.StoppedWord) (h : word.1 = 0) :
    word = ⟨0, Fin.elim0⟩ := by
  rcases word with ⟨n, f⟩
  change n = 0 at h
  subst n
  congr 1
  funext k
  exact Fin.elim0 k

theorem preReportWord_eq_validWord (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (hv : P.ValidCutHistory order history)
    (stage : (starInstance P.tools order).Stage) :
    P.preReportWord order history stage = historyObservationWord (P.input order) history stage (hv stage) := by
  classical
  unfold preReportWord
  by_cases hn : historyObservations history stage = []
  · rw [ite_eq_left hn]
    symm
    apply emptyWord_of_length_zero
    change (historyObservations history stage).length = 0
    rw [hn]
    rfl
  · rw [ite_eq_right hn, dite_eq_left (hv stage)]
    rfl

noncomputable def completedCutTapes (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) : ReviewTapes (P.input order) :=
  fun stage => P.channel.experiment.completeStoppedWord (P.preReportWord order history stage)

theorem completedCutTapes_mem_cylinder (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (hv : P.ValidCutHistory order history) :
    P.completedCutTapes order history ∈ publicWordCylinder (P.input order) history := by
  apply (publicWordCylinder_iff_prefixEvents (P.input order) history hv _).mpr
  intro stage k
  change P.channel.experiment.completeStoppedWord (P.preReportWord order history stage) k.val = _
  rw [P.preReportWord_eq_validWord order history hv stage]
  exact P.channel.experiment.completeStoppedWord_prefix _ _ _ k.isLt

noncomputable def cutLikelihood (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (truth : (starInstance P.tools order).Stage → Bool) : ℝ≥0∞ :=
  ∏ stage, P.channel.experiment.priorMass (truth stage) *
    ENNReal.ofReal (P.channel.experiment.wordProbability (truth stage) (P.preReportWord order history stage))

noncomputable def cutPosterior (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (truth : (starInstance P.tools order).Stage → Bool) : ℝ≥0∞ :=
  ∏ stage, P.preReportPosteriorMass order history stage (truth stage)

private theorem ofReal_half : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem localPosterior_mul_evidence (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (x : Bool) :
    P.preReportPosteriorMass order history stage x *
      (∑ y : Bool, P.channel.experiment.priorMass y *
        ENNReal.ofReal (P.channel.experiment.wordProbability y (P.preReportWord order history stage))) =
      P.channel.experiment.priorMass x *
        ENNReal.ofReal (P.channel.experiment.wordProbability x (P.preReportWord order history stage)) := by
  let word := P.preReportWord order history stage
  have hsum : (∑ y : Bool, P.channel.experiment.priorMass y * ENNReal.ofReal (P.channel.experiment.wordProbability y word)) =
      ENNReal.ofReal (P.channel.wordEvidence word / 2) := by
    simp only [P.channel.priorMass_eq_half, Fintype.sum_bool]
    rw [← ofReal_half, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_add
        (mul_nonneg (by norm_num) (P.channel.experiment.wordProbability_pos true word).le)
        (mul_nonneg (by norm_num) (P.channel.experiment.wordProbability_pos false word).le)]
    congr 1
    unfold BinarySymmetric.Parameters.wordEvidence
    ring
  have hreal : P.channel.wordPosteriorMass x word * (P.channel.wordEvidence word / 2) =
      (1 / 2 : ℝ) * P.channel.experiment.wordProbability x word := by
    unfold BinarySymmetric.Parameters.wordPosteriorMass
    field_simp [(P.channel.wordEvidence_pos word).ne']
  change ENNReal.ofReal (P.channel.wordPosteriorMass x word) * _ = _
  rw [hsum, ← ENNReal.ofReal_mul (P.channel.wordPosteriorMass_pos x word).le, hreal,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ofReal_half, P.channel.priorMass_eq_half]

theorem cutPosterior_normalization (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (truth : (starInstance P.tools order).Stage → Bool) :
    P.cutPosterior order history truth * (∑ bits, P.cutLikelihood order history bits) =
      P.cutLikelihood order history truth := by
  unfold cutLikelihood
  have hsum : (∑ bits : (starInstance P.tools order).Stage → Bool,
      ∏ stage, P.channel.experiment.priorMass (bits stage) *
        ENNReal.ofReal (P.channel.experiment.wordProbability (bits stage) (P.preReportWord order history stage))) =
      ∏ stage, ∑ x : Bool, P.channel.experiment.priorMass x *
        ENNReal.ofReal (P.channel.experiment.wordProbability x (P.preReportWord order history stage)) :=
    (Fintype.prod_sum (fun (stage : (starInstance P.tools order).Stage) (x : Bool) =>
      P.channel.experiment.priorMass x *
        ENNReal.ofReal (P.channel.experiment.wordProbability x (P.preReportWord order history stage)))).symm
  rw [hsum]
  unfold cutPosterior
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun stage _ => P.localPosterior_mul_evidence order history stage (truth stage)

section Seed

variable {Seed : Type u} [MeasurableSpace Seed]

noncomputable def cutSeedGate (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed)
    (history : List (VisibleEvent (starInstance P.tools order))) : Set Seed :=
  preReportSeedGate (P.input order) C accounting rule (fun _ => false) (P.completedCutTapes order history) history

omit [MeasurableSpace Seed] in
theorem invalid_cutGate_empty (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (history : List (VisibleEvent (starInstance P.tools order))) (hv : ¬ P.ValidCutHistory order history) :
    P.cutSeedGate order C accounting rule history = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro seed hs
  apply hv
  have heq : preReportPublicHistory (P.input order) C accounting rule
      (seed, replayWorld (P.input order) (fun _ => false) (P.completedCutTapes order history)) = history := hs
  intro i symbol hsymbol
  exact preReportPublicHistory_observation_alphabet (P.input order) C accounting rule hlegal _ i symbol
    (heq ▸ hsymbol)

def jointCutEvent (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (seeds : Set Seed)
    (history : List (VisibleEvent (starInstance P.tools order))) (truth : (starInstance P.tools order).Stage → Bool) :
    Set (Seed × (P.input order).World) :=
  {sample | sample.1 ∈ seeds ∧ (P.input order).truthAt sample.2 = truth ∧
    preReportPublicHistory (P.input order) C accounting rule sample = history}

theorem measurableSet_jointCutEvent (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule) (seeds : Set Seed) (hs : MeasurableSet seeds)
    (history : List (VisibleEvent (starInstance P.tools order))) (truth : (starInstance P.tools order).Stage → Bool) :
    MeasurableSet (P.jointCutEvent order C accounting rule seeds history truth) := by
  have htruth : Measurable (fun sample : Seed × (P.input order).World => (P.input order).truthAt sample.2) :=
    measurable_pi_iff.mpr fun stage => ((P.input order).measurable_truthAt stage).comp measurable_snd
  exact (hs.preimage measurable_fst).inter
    ((htruth (measurableSet_singleton truth)).inter
      ((measurable_preReportPublicHistory (P.input order) C accounting rule hm) (measurableSet_singleton history)))

theorem jointCutEvent_law (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) (rule : PolicyRule (starInstance P.tools order) Seed)
    (hm : MeasurableRule rule) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (seeds : Set Seed) (hs : MeasurableSet seeds)
    (history : List (VisibleEvent (starInstance P.tools order))) (truth : (starInstance P.tools order).Stage → Bool) :
    (P.input order).seededWorldLaw ν (P.jointCutEvent order C accounting rule seeds history truth) =
      ν (seeds ∩ P.cutSeedGate order C accounting rule history) * P.cutLikelihood order history truth := by
  classical
  by_cases hv : P.ValidCutHistory order history
  · have h := (preReport_jointTruth_seedEvent_law (P.input order) C hlate accounting rule hm hlegal ν
      (fun _ => false) truth (P.completedCutTapes order history) history
      (P.completedCutTapes_mem_cylinder order history hv) hv seeds hs).2
    simp_rw [← P.preReportWord_eq_validWord order history hv] at h
    exact h
  · have hempty : P.jointCutEvent order C accounting rule seeds history truth = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hsample
      apply hv
      intro i symbol hsymbol
      exact preReportPublicHistory_observation_alphabet (P.input order) C accounting rule hlegal sample i symbol
        (hsample.2.2 ▸ hsymbol)
    rw [hempty, P.invalid_cutGate_empty order C accounting rule hlegal history hv]
    simp

/-- Sum the finite truth partition at one public history. All seed sets in
this rectangle may be arbitrary measurable sets, including mass-zero sets. -/
theorem preReportLaw_rectangle (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) (rule : PolicyRule (starInstance P.tools order) Seed)
    (hm : MeasurableRule rule) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (seeds : Set Seed) (hs : MeasurableSet seeds)
    (history : List (VisibleEvent (starInstance P.tools order))) :
    preReportLaw (P.input order) C accounting rule ν (seeds ×ˢ {history}) =
      ν (seeds ∩ P.cutSeedGate order C accounting rule history) * (∑ truth, P.cutLikelihood order history truth) := by
  classical
  rw [preReportLaw, Measure.map_apply (measurable_preReportRecord (P.input order) C accounting rule hm)
    (hs.prod (measurableSet_singleton history))]
  have heq : (preReportRecord (P.input order) C accounting rule) ⁻¹' (seeds ×ˢ {history}) =
      ⋃ truth, P.jointCutEvent order C accounting rule seeds history truth := by
    ext sample
    change (sample.1 ∈ seeds ∧ preReportPublicHistory (P.input order) C accounting rule sample = history) ↔ _
    simp only [Set.mem_iUnion, jointCutEvent, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hseed, hh⟩
      exact ⟨(P.input order).truthAt sample.2, hseed, rfl, hh⟩
    · rintro ⟨truth, hseed, _, hh⟩
      exact ⟨hseed, hh⟩
  have hdisj : Pairwise (fun truth truth' => Disjoint
      (P.jointCutEvent order C accounting rule seeds history truth)
      (P.jointCutEvent order C accounting rule seeds history truth')) := by
    intro truth truth' hne
    apply Set.disjoint_left.mpr
    intro sample hleft hright
    exact hne (hleft.2.1.symm.trans hright.2.1)
  rw [heq, measure_iUnion hdisj (fun truth => P.measurableSet_jointCutEvent order C accounting rule hm seeds hs history truth),
    tsum_fintype]
  simp_rw [P.jointCutEvent_law order C hlate accounting rule hm hlegal ν seeds hs history]
  rw [Finset.mul_sum]

/-- Joint law of the real record and a fixed complete truth assignment,
defined by restriction of the original world law before pushforward. -/
noncomputable def cutTruthRecordLaw (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (ν : Measure Seed)
    (truth : (starInstance P.tools order).Stage → Bool) :
    Measure (Seed × List (VisibleEvent (starInstance P.tools order))) :=
  (((P.input order).seededWorldLaw ν).restrict {sample | (P.input order).truthAt sample.2 = truth}).map
    (preReportRecord (P.input order) C accounting rule)

theorem cutTruthRecordLaw_apply (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (rule : PolicyRule (starInstance P.tools order) Seed) (hm : MeasurableRule rule) (ν : Measure Seed)
    (truth : (starInstance P.tools order).Stage → Bool)
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hB : MeasurableSet B) :
    P.cutTruthRecordLaw order C accounting rule ν truth B =
      (P.input order).seededWorldLaw ν
        {sample | preReportRecord (P.input order) C accounting rule sample ∈ B ∧
          (P.input order).truthAt sample.2 = truth} := by
  rw [cutTruthRecordLaw, Measure.map_apply (measurable_preReportRecord (P.input order) C accounting rule hm) hB,
    Measure.restrict_apply (hB.preimage (measurable_preReportRecord (P.input order) C accounting rule hm))]
  rfl

theorem cutTruthRecordLaw_rectangle (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) (rule : PolicyRule (starInstance P.tools order) Seed)
    (hm : MeasurableRule rule) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (seeds : Set Seed) (hs : MeasurableSet seeds)
    (history : List (VisibleEvent (starInstance P.tools order))) (truth : (starInstance P.tools order).Stage → Bool) :
    P.cutTruthRecordLaw order C accounting rule ν truth (seeds ×ˢ {history}) =
      P.cutPosterior order history truth * preReportLaw (P.input order) C accounting rule ν (seeds ×ˢ {history}) := by
  rw [P.cutTruthRecordLaw_apply order C accounting rule hm ν truth _ (hs.prod (measurableSet_singleton history))]
  have heq : {sample : Seed × (P.input order).World |
      preReportRecord (P.input order) C accounting rule sample ∈ seeds ×ˢ {history} ∧
        (P.input order).truthAt sample.2 = truth} = P.jointCutEvent order C accounting rule seeds history truth := by
    ext sample
    simp only [preReportRecord, Set.mem_prod, Set.mem_singleton_iff, jointCutEvent, Set.mem_ofPred_eq]
    exact and_assoc.trans (and_congr_right fun _ => and_comm)
  rw [heq, P.jointCutEvent_law order C hlate accounting rule hm hlegal ν seeds hs history truth,
    P.preReportLaw_rectangle order C hlate accounting rule hm hlegal ν seeds hs history]
  rw [mul_left_comm (P.cutPosterior order history truth), P.cutPosterior_normalization]

/-- Full record-space measure identity. Countability is used only for public
histories; no countability or singleton-mass assumption is made on Seed. -/
theorem cutTruthRecordLaw_eq_withDensity (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) (rule : PolicyRule (starInstance P.tools order) Seed)
    (hm : MeasurableRule rule) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (truth : (starInstance P.tools order).Stage → Bool) :
    P.cutTruthRecordLaw order C accounting rule ν truth =
      (preReportLaw (P.input order) C accounting rule ν).withDensity
        (fun record => P.cutPosterior order record.2 truth) := by
  have : IsFiniteMeasure (P.cutTruthRecordLaw order C accounting rule ν truth) := by
    unfold cutTruthRecordLaw
    infer_instance
  apply Measure.ext_prod
  intro seeds histories hs _hh
  have hset : seeds ×ˢ histories = ⋃ history : histories, seeds ×ˢ {history.val} := by
    ext record
    simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hseed, hh⟩
      exact ⟨⟨record.2, hh⟩, hseed, rfl⟩
    · rintro ⟨history, hseed, hh⟩
      exact ⟨hseed, hh ▸ history.property⟩
  have hdisj : Pairwise (fun history history' : histories =>
      Disjoint (seeds ×ˢ {history.val}) (seeds ×ˢ {history'.val})) := by
    intro history history' hne
    apply Set.disjoint_left.mpr
    intro record hr hr'
    exact hne (Subtype.ext (hr.2.symm.trans hr'.2))
  have hmeas (history : histories) : MeasurableSet (seeds ×ˢ {history.val}) := hs.prod (measurableSet_singleton _)
  rw [hset, measure_iUnion hdisj hmeas, measure_iUnion hdisj hmeas]
  apply tsum_congr
  intro history
  rw [withDensity_apply _ (hmeas history)]
  have hconstant : (∫⁻ record in seeds ×ˢ {history.val}, P.cutPosterior order record.2 truth
      ∂preReportLaw (P.input order) C accounting rule ν) =
      P.cutPosterior order history.val truth *
        preReportLaw (P.input order) C accounting rule ν (seeds ×ˢ {history.val}) := by
    calc
      _ = ∫⁻ _record in seeds ×ˢ {history.val}, P.cutPosterior order history.val truth
          ∂preReportLaw (P.input order) C accounting rule ν := by
        apply setLIntegral_congr_fun (hmeas history)
        intro record hr
        change P.cutPosterior order record.2 truth = P.cutPosterior order history.val truth
        rw [hr.2]
      _ = _ := by simp
  rw [hconstant]
  exact P.cutTruthRecordLaw_rectangle order C hlate accounting rule hm hlegal ν seeds hs history.val truth

theorem preReport_truth_event_integral (P : Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (hlate : C.reporting = .late)
    (accounting : NormalAccounting (starInstance P.tools order)) (rule : PolicyRule (starInstance P.tools order) Seed)
    (hm : MeasurableRule rule) (hlegal : LegalRule (P.input order) C .native accounting rule)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) (hB : MeasurableSet B)
    (truth : (starInstance P.tools order).Stage → Bool) :
    (P.input order).seededWorldLaw ν
      {sample | preReportRecord (P.input order) C accounting rule sample ∈ B ∧
        (P.input order).truthAt sample.2 = truth} =
      ∫⁻ record, B.indicator (fun record => P.cutPosterior order record.2 truth) record
        ∂preReportLaw (P.input order) C accounting rule ν := by
  rw [← P.cutTruthRecordLaw_apply order C accounting rule hm ν truth B hB,
    P.cutTruthRecordLaw_eq_withDensity order C hlate accounting rule hm hlegal ν truth,
    withDensity_apply _ hB, lintegral_indicator hB]

end Seed

/-- C04 for the original two orders, all original late-retained contracts,
all private seed universes and ALL measurable Seed x public-history events. -/
theorem preReportProductPosterior (P : Star.Parameters) : P.PreReportProductPosterior.{u} := by
  intro order C hlate accounting Seed m ν hν policy B hB truth
  exact P.preReport_truth_event_integral order C hlate.1 accounting policy.rule policy.measurable_rule policy.legal ν B hB truth

end PaperProofs.Star.Parameters
