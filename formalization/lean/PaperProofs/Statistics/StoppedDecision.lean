module

public import PaperProofs.Statistics.DecisionLaw
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Order.SuccPred.ENat

/-!
Reconstructing a finite stopped decision from its actual seed and observed
word. The information identity itself remains unproved. The final theorem
states its implication to the decision-information bound explicitly.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinaryExperiment

theorem stopping_preserved_by_prefix (E : BinaryExperiment) {Seed : Type*}
    (rule : E.SequentialRule Seed) (seed : Seed) (tape tape' : E.Tape) (n : ℕ)
    (hstop : rule.stop seed tape = n) (hprefix : ∀ k < n, tape k = tape' k) :
    rule.stop seed tape' = n := by
  have hle : rule.stop seed tape' ≤ n :=
    (rule.stopping seed tape tape' n hprefix).mp (by rw [hstop])
  cases n with
  | zero => exact le_antisymm hle zero_le
  | succ n =>
    have hnot : ¬ rule.stop seed tape' ≤ n := by
      intro h
      have hprefix' : ∀ k < n, tape k = tape' k :=
        fun k hk => hprefix k (Nat.lt_succ_of_lt hk)
      have horig := (rule.stopping seed tape tape' n hprefix').mpr h
      rw [hstop] at horig
      exact Nat.not_succ_le_self n (ENat.natCast_le_natCast.mp horig)
    apply le_antisymm hle
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot))

/-- The existing sigma measurable space is discrete because each word fiber is finite.
This proves a property of that space; it does not install a different measurable space. -/
instance stoppedWord_discrete (E : BinaryExperiment) : DiscreteMeasurableSpace E.StoppedWord := by
  constructor
  intro s
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → Fin E.alphabetSize)).map (Sigma.mk n)] s
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((Sigma.mk n) ⁻¹' s)
  exact (Set.toFinite _).measurableSet

/-- A completion symbol is needed only by this analysis map, not by the controller. -/
noncomputable def completionSymbol (E : BinaryExperiment) : Fin E.alphabetSize :=
  Classical.choose (E.channelPMF false).support_nonempty

noncomputable def completeStoppedWord (E : BinaryExperiment) (word : E.StoppedWord) : E.Tape :=
  fun k => if hk : k < word.1 then word.2 ⟨k, hk⟩ else E.completionSymbol

theorem completeStoppedWord_prefix (E : BinaryExperiment) (n : ℕ)
    (word : Fin n → Fin E.alphabetSize) (k : ℕ) (hk : k < n) :
    E.completeStoppedWord ⟨n, word⟩ k = word ⟨k, hk⟩ := by
  simp [completeStoppedWord, hk]

section PrivateSeed

variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def decodedStoppedDecision (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (record : Seed × E.StoppedWord) : Bool :=
  test.rule.decision record.1 (E.completeStoppedWord record.2)

theorem measurable_decodedStoppedDecision (E : BinaryExperiment) (test : E.AdmissibleRule Seed) :
    Measurable (E.decodedStoppedDecision test) := by
  exact test.measurable_decision.comp
    (measurable_fst.prodMk ((measurable_of_countable E.completeStoppedWord).comp measurable_snd))

theorem stoppedWord_eq_iff (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) (n : ℕ) (word : Fin n → Fin E.alphabetSize) :
    (⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩ : E.StoppedWord) =
        ⟨n, word⟩ ↔
      (test.rule.stop sample.1 sample.2).toNat = n ∧
        ∀ k : Fin n, sample.2 k.val = word k := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨hn, hw⟩
    subst n
    congr 1
    exact funext hw

theorem measurable_stoppedTranscript (E : BinaryExperiment) (test : E.AdmissibleRule Seed) :
    Measurable (E.stoppedTranscript test) := by
  have hword : Measurable (fun sample : Seed × E.Tape =>
      (⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩ : E.StoppedWord)) := by
    apply measurable_to_countable'
    rintro ⟨n, word⟩
    have hset :
        (fun sample : Seed × E.Tape =>
          (⟨(test.rule.stop sample.1 sample.2).toNat, fun k => sample.2 k.val⟩ : E.StoppedWord)) ⁻¹'
            {⟨n, word⟩} =
          {sample : Seed × E.Tape | (test.rule.stop sample.1 sample.2).toNat = n} ∩
            ⋂ k : Fin n, {sample : Seed × E.Tape | sample.2 k.val = word k} := by
      ext sample
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
        Set.mem_ofPred_eq, Set.mem_iInter] using E.stoppedWord_eq_iff test sample n word
    rw [hset]
    have hlength : Measurable (fun sample : Seed × E.Tape =>
        (test.rule.stop sample.1 sample.2).toNat) :=
      (measurable_of_countable ENat.toNat).comp test.measurable_stop
    refine (hlength (measurableSet_singleton n)).inter (MeasurableSet.iInter fun k => ?_)
    exact (measurableSet_singleton (word k)).preimage
      ((measurable_pi_apply k.val).comp measurable_snd)
  exact measurable_fst.prodMk hword

theorem transcriptLaw_apply (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (s : Set (Seed × E.StoppedWord))
    (hs : MeasurableSet s) :
    E.transcriptLaw ν test x s =
      E.conditionalLaw ν x ((E.stoppedTranscript test) ⁻¹' s) :=
  Measure.map_apply (E.measurable_stoppedTranscript test) hs

instance transcriptLaw_probability (E : BinaryExperiment) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (test : E.AdmissibleRule Seed) (x : Bool) :
    IsProbabilityMeasure (E.transcriptLaw ν test x) := by
  constructor
  rw [E.transcriptLaw_apply ν test x Set.univ MeasurableSet.univ]
  simp

theorem decodedStoppedDecision_eq (E : BinaryExperiment) (test : E.AdmissibleRule Seed)
    (sample : Seed × E.Tape) (hfinite : test.rule.stop sample.1 sample.2 ≠ ⊤) :
    E.decodedStoppedDecision test (E.stoppedTranscript test sample) =
      test.rule.decision sample.1 sample.2 := by
  let n := (test.rule.stop sample.1 sample.2).toNat
  let completed := E.completeStoppedWord ⟨n, fun k => sample.2 k.val⟩
  have hstop : test.rule.stop sample.1 sample.2 = n := (ENat.natCast_toNat hfinite).symm
  have hprefix : ∀ k < n, sample.2 k = completed k := by
    intro k hk
    simp [completed, completeStoppedWord, hk]
  have hcompleted := E.stopping_preserved_by_prefix test.rule sample.1 sample.2 completed n
    hstop hprefix
  exact (test.rule.stoppedDecision sample.1 sample.2 completed n hstop hcompleted hprefix).symm

theorem decodedStoppedDecision_ae (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    (fun sample => E.decodedStoppedDecision test (E.stoppedTranscript test sample)) =ᵐ[
      E.conditionalLaw ν x] (fun sample => test.rule.decision sample.1 sample.2) := by
  filter_upwards [E.expectedSamples_finite_stop ν test x hfinite] with sample hsample
  exact E.decodedStoppedDecision_eq test sample hsample

theorem transcriptLaw_decodedDecision (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool) (hfinite : E.expectedSamples ν test x ≠ ⊤) :
    (E.transcriptLaw ν test x).map (E.decodedStoppedDecision test) = E.decisionLaw ν test x := by
  unfold transcriptLaw decisionLaw
  rw [Measure.map_map (E.measurable_decodedStoppedDecision test) (E.measurable_stoppedTranscript test)]
  exact Measure.map_congr (E.decodedStoppedDecision_ae ν test x hfinite)

end PrivateSeed

/-- Conditional connection only: the stopped-information identity is the explicit
outstanding premise. Reconstruction, measurability and data processing are proved here. -/
theorem stoppedDecisionInformationBound_of_identity (E : BinaryExperiment)
    (hidentity : E.StoppedInformationIdentity) : E.StoppedDecisionInformationBound := by
  intro Seed m
  let : MeasurableSpace Seed := m
  intro ν hν test hfinite x
  have : IsProbabilityMeasure ν := hν
  have hinfo := hidentity Seed m ν hν test hfinite
  have hkl := InformationTheory.klDiv_map_le (E.transcriptLaw ν test x)
    (E.transcriptLaw ν test (!x)) (E.measurable_decodedStoppedDecision test)
  rw [E.transcriptLaw_decodedDecision ν test x (hfinite x),
    E.transcriptLaw_decodedDecision ν test (!x) (hfinite (!x)), hinfo.2 x] at hkl
  exact hkl

end PaperProofs.Statistics.BinaryExperiment
