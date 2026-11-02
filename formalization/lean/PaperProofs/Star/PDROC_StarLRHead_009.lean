module

public import PaperProofs.Star.PDROC_StarLRHead_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem star_mismatch_card_le_of_head_correct (P : PaperProofs.Star.Parameters) (order : Order)
    (ledger : Ledger (starInstance P.tools order))
    (correct : ledger.written (firstStage P.tools order) =
      some (ledger.truth (firstStage P.tools order))) :
    (PaperProofs.Retained.ordinaryMismatches ledger).card ≤ P.tools := by
  classical
  have headNot : firstStage P.tools order ∉ PaperProofs.Retained.ordinaryMismatches ledger := by
    intro wrong
    have equation := (PaperProofs.Retained.mem_ordinaryMismatches ledger _).mp wrong
    rw [correct] at equation
    have impossible := Option.some.inj equation
    exact (Bool.eq_not_self _).mp impossible
  have subset : PaperProofs.Retained.ordinaryMismatches ledger ⊆
      (Finset.univ : Finset (starInstance P.tools order).Stage).erase (firstStage P.tools order) := by
    intro stage wrong
    exact Finset.mem_erase.mpr ⟨fun equal => headNot (equal ▸ wrong), Finset.mem_univ _⟩
  have bound := Finset.card_le_card subset
  have size : (Finset.univ : Finset (starInstance P.tools order).Stage).card = P.tools+1 := by
    simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin]
    exact stageCount_eq P.tools order
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), size] at bound
  omega

theorem original_risk_le_of_terminalCriterion (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) {r : ℝ}
    (hr : 0 < r) (hrquarter : r ≤ 1/4)
    (terminal : P.TerminalCriterion order .lateRetained r C accounting) :
    risk (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)) (Measure.dirac ()) ≤ ENNReal.ofReal r := by
  classical
  let R := run (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none (Seed := Unit))
  let failed : Unit × (P.input order).World → ℝ≥0∞ := fun sample =>
    if ¬ runSuccess (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample then 1 else 0
  let error : Unit × (P.input order).World → ℝ≥0∞ := fun sample =>
    if (referenceHeadTest P order r).rule.decision sample.1
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) ≠
      (P.input order).truthAt sample.2 (firstStage P.tools order) then 1 else 0
  have legal := PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r none C
    late.2.1 late.2.2 accounting (Seed := Unit)
  have comparison : ∀ᵐ sample ∂(P.input order).seededWorldLaw (Measure.dirac ()), failed sample ≤ error sample := by
    filter_upwards [terminal] with sample terminalSample
    obtain ⟨time, halted, complete, criterion, _⟩ := terminalSample
    by_cases wrong : (referenceHeadTest P order r).rule.decision sample.1
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) ≠
        (P.input order).truthAt sample.2 (firstStage P.tools order)
    · simp only [error, ite_eq_left wrong]
      dsimp only [failed]
      split_ifs <;> norm_num
    · have known := complete (firstStage P.tools order)
      obtain ⟨bit, written⟩ := Option.ne_none_iff_exists'.mp known
      have decision := nativeHead_decision_of_written (P.input order) C accounting
        (P.starReferenceRule order .lateRetained r none) legal (firstStage P.tools order) rfl
        sample time bit written
      have correctBit : bit = (P.input order).truthAt sample.2 (firstStage P.tools order) :=
        decision.symm.trans (not_ne_iff.mp wrong)
      obtain ⟨clock, _, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) legal sample time
      have truth := congrFun (prefix_truth (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path) (firstStage P.tools order)
      have correct : (R sample time).ledger.written (firstStage P.tools order) =
          some ((R sample time).ledger.truth (firstStage P.tools order)) :=
        written.trans (congrArg some (correctBit.trans truth.symm))
      have count := star_mismatch_card_le_of_head_correct P order (R sample time).ledger correct
      have success : runSuccess (P.input order) C .uncapped accounting
          (P.starReferenceRule order .lateRetained r none) sample :=
        ⟨time, halted, criterion.mpr count⟩
      simp only [failed, ite_eq_right (not_not.mpr success)]
      exact bot_le
  have measurableFailure : MeasurableSet {sample : Unit × (P.input order).World |
      ¬ runSuccess (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample} :=
    (measurableSet_runSuccess (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none)
      (P.measurable_starReferenceRule order .lateRetained r none)).compl
  have riskIntegral : risk (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)) (Measure.dirac ()) =
      ∫⁻ sample, failed sample ∂(P.input order).seededWorldLaw (Measure.dirac ()) := by
    unfold risk
    simpa only [failed, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
      (lintegral_indicator_one (μ := (P.input order).seededWorldLaw (Measure.dirac ())) measurableFailure).symm
  exact riskIntegral.le.trans ((lintegral_mono_ae comparison).trans
    (referenceHeadTest_error_world_le P order hr (by linarith)))

end PDROC.StarLRHead
