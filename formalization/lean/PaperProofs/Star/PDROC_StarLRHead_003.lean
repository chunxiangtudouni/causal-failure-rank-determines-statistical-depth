module

public import PaperProofs.Star.PDROC_StarLRHead_002
public import PaperProofs.Star.PStarLR_PrefixFrame_003
public import PaperProofs.Common.NativeHeadAccounting

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

theorem reference_run_other_reviews_zero (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)))
    (sample : Unit × (P.input order).World) (n : ℕ) (other : (starInstance P.tools order).Stage)
    (nonhead : other ≠ firstStage P.tools order) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n).ledger.reviews other = 0 := by
  exact PStarLR.late_run_other_reviews_zero_of_legal P order r none C .uncapped accounting
    legal sample n other (fun zero => nonhead (Fin.ext zero))

theorem reference_run_write_data (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = n) :
    let stage := firstStage P.tools order
    let tape := (P.input order).reviewAt sample.2 stage
    let bit := (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () tape
    let state := run (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample (n+1)
    state.ledger.written stage = some bit ∧ state.ledger.reviews stage = n ∧ state.cursor = 0 := by
  dsimp only
  rw [reference_run_write_at_stop P order r C accounting sample n stop]
  constructor
  · classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> simp only [writeLedger, Function.update_self]
  · constructor
    · classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact headReviewState_reviews (P.input order) accounting _ _ _ n
    · rfl

theorem reference_run_head_reviews_le_stop (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)))
    (sample : Unit × (P.input order).World) (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = n) (k : ℕ) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
      sample k).ledger.reviews (firstStage P.tools order) ≤ n := by
  by_cases early : k ≤ n
  · have before := reference_run_before_stop P order r C accounting sample k
      (by rw [stop]; exact_mod_cast early)
    rw [before, headReviewState_reviews]
    exact_mod_cast early
  · have later : n + 1 ≤ k := by omega
    obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le later
    have data := reference_run_write_data P order r C accounting sample n stop
    have count := run_reviews_written_port (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) legal sample (n+1) extra
      (firstStage P.tools order) _ data.1
    rw [← equal, data.2.1] at count
    exact count.le

theorem reference_run_prefix_observationBill (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)))
    (sample : Unit × (P.input order).World) (k : ℕ) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
      sample k).ledger.observationBill (P.input order).fees =
      ENNReal.ofReal (P.channel.reviewFee : ℝ) *
        ((run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
          sample k).ledger.reviews (firstStage P.tools order)).toENNReal := by
  classical
  unfold Ledger.observationBill
  rw [Finset.sum_eq_single (firstStage P.tools order)]
  · rfl
  · intro other _ distinct
    rw [reference_run_other_reviews_zero P order r C accounting legal sample k other distinct,
      ENat.toENNReal_zero, mul_zero]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

theorem reference_runObservationBill_eq (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none (Seed := Unit)))
    (sample : Unit × (P.input order).World) :
    runObservationBill (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) sample =
      P.channel.experiment.observationCharge (realPosteriorStop P.channel.experiment r
        ((P.input order).reviewAt sample.2 (firstStage P.tools order))) := by
  apply le_antisymm
  · by_cases infinite : realPosteriorStop P.channel.experiment r
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = ⊤
    · rw [infinite, PaperProofs.Statistics.BinaryExperiment.observationCharge_top]
      exact le_top
    · generalize stop : realPosteriorStop P.channel.experiment r
        ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = time at infinite ⊢
      lift time to ℕ using infinite with n
      rw [PaperProofs.Statistics.BinaryExperiment.observationCharge_nat]
      apply iSup_le
      intro k
      rw [reference_run_prefix_observationBill P order r C accounting legal sample k]
      change ENNReal.ofReal (P.channel.reviewFee : ℝ) *
        ((run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
          sample k).ledger.reviews (firstStage P.tools order)).toENNReal ≤
        ENNReal.ofReal (P.channel.reviewFee : ℝ) * (n : ℝ≥0∞)
      exact mul_le_mul_right (ENat.toENNReal_mono
        (reference_run_head_reviews_le_stop P order r C accounting legal sample n stop k))
        (ENNReal.ofReal (P.channel.reviewFee : ℝ))
  · have lower := nativeHead_observationCharge_le (P.input order) C accounting
      (P.starReferenceRule order .lateRetained r none) (firstStage P.tools order) rfl sample
    cases sample.1
    exact (congrArg P.channel.experiment.observationCharge
      (reference_head_stop P order r _)).symm.le.trans lower

end PDROC.StarLRHead
