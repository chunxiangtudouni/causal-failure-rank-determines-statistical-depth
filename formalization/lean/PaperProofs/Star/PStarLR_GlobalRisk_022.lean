module

public import PaperProofs.Star.PStarLR_PostHeadCompletion_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

variable {I : Instance}

theorem run_written_agree (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (legal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (left right : ℕ) (stage : I.Stage) (leftBit rightBit : Bool)
    (leftWrite : (run input C mode accounting rule sample left).ledger.written stage = some leftBit)
    (rightWrite : (run input C mode accounting rule sample right).ledger.written stage = some rightBit) :
    leftBit = rightBit := by
  rcases le_total left right with later | earlier
  · have still := run_written_some_after input C mode accounting rule legal sample left (right-left) stage leftBit leftWrite
    rw [Nat.add_sub_of_le later] at still
    exact Option.some.inj (still.symm.trans rightWrite)
  · have still := run_written_some_after input C mode accounting rule legal sample right (left-right) stage rightBit rightWrite
    rw [Nat.add_sub_of_le earlier] at still
    exact Option.some.inj (leftWrite.symm.trans still)

theorem late_risk_le_head_error (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order))
    (decision : Unit × (P.input order).World → Bool)
    (headWritten : ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())), ∃ start,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
        sample start).ledger.written (firstStage P.tools order) = some (decision sample)) :
    risk (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
      (Measure.dirac ()) ≤
      ∫⁻ sample : Unit × (P.input order).World,
        (if decision sample ≠ (P.input order).truthAt sample.2 (firstStage P.tools order)
          then (1 : ℝ≥0∞) else 0) ∂(P.input order).seededWorldLaw (Measure.dirac ()) := by
  classical
  have legal := retained_legal_uncapped P order .lateRetained (by decide) r none C late.2.1 late.2.2 accounting
    (Seed := Unit)
  have headAny : ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())), ∃ start bit,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
        sample start).ledger.written (firstStage P.tools order) = some bit := by
    filter_upwards [headWritten] with sample written
    obtain ⟨start, written⟩ := written
    exact ⟨start, decision sample, written⟩
  have terminal := late_terminalCriterion_of_ae_head_write P order r C late accounting headAny
  have failureToError : ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())),
      ¬ runSuccess (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample →
        decision sample ≠ (P.input order).truthAt sample.2 (firstStage P.tools order) := by
    filter_upwards [terminal, headWritten] with sample terminal written
    obtain ⟨n, halted, complete, successIff, _count⟩ := terminal
    obtain ⟨start, written⟩ := written
    intro failure correct
    have good : (PaperProofs.Retained.ordinaryMismatches
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n).ledger).card ≤ P.tools := by
      by_contra bad
      have whole : PaperProofs.Retained.ordinaryMismatches
          (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n).ledger =
          (Finset.univ : Finset (starInstance P.tools order).Stage) := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        have total : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools+1 := by
          simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
          exact stageCount_eq P.tools order
        rw [total]
        exact Nat.succ_le_of_lt (Nat.lt_of_not_ge bad)
      have wrong : (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
          sample n).ledger.written (firstStage P.tools order) =
          some (!(run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
            sample n).ledger.truth (firstStage P.tools order)) := by
        apply (PaperProofs.Retained.mem_ordinaryMismatches _ _).mp
        rw [whole]
        exact Finset.mem_univ _
      obtain ⟨_clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) legal sample n
      have actualTruth := prefix_truth (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample.1 ((P.input order).truthAt sample.2)
        (worldTapes (P.input order) sample.2) path
      rw [actualTruth] at wrong
      have equal := run_written_agree (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) legal sample start n (firstStage P.tools order)
        (decision sample) _ written wrong
      rw [correct] at equal
      cases truth : (P.input order).truthAt sample.2 (firstStage P.tools order) <;> simp [truth] at equal
    exact failure ⟨n, halted, successIff.mpr good⟩
  have measurableFailure : MeasurableSet {sample : Unit × (P.input order).World |
      ¬runSuccess (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample} :=
    (measurableSet_runSuccess (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) (P.measurable_starReferenceRule order .lateRetained r none)).compl
  have integralRisk : (∫⁻ sample : Unit × (P.input order).World,
      (if ¬runSuccess (P.input order) C .uncapped accounting
          (P.starReferenceRule order .lateRetained r none) sample then (1 : ℝ≥0∞) else 0)
        ∂(P.input order).seededWorldLaw (Measure.dirac ())) =
      risk (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) (Measure.dirac ()) := by
    simpa only [Set.indicator_apply, Set.mem_ofPred_eq, one_mul, risk] using
      (lintegral_indicator_const (μ := (P.input order).seededWorldLaw (Measure.dirac ())) measurableFailure 1)
  rw [← integralRisk]
  apply lintegral_mono_ae
  filter_upwards [failureToError] with sample implication
  by_cases failure : ¬runSuccess (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample
  · have error := implication failure
    simp [failure, error]
  · simp [failure]

end PStarLR
