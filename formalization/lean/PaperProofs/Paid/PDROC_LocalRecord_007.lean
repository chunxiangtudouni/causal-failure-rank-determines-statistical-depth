module
public import PaperProofs.Paid.PDROC_LocalRecord_006
public import PaperProofs.Common.NativeHeadAccounting
public import PaperProofs.Common.ReferenceObservationCost

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Statistics

namespace PDROC
universe u
variable {I : Instance} {Seed : Type u}

private theorem reportedWrite_reviews_unchanged (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- At every finite local exit, write, stop and abandon all freeze the real
head review counter at exactly the extracted stop count. -/
theorem nativeHead_reviews_after_exit (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = n) (extra : ℕ) :
    (run input C .uncapped accounting rule sample (n + extra)).ledger.reviews head = n := by
  have hr := run_eq_headReviewState input C accounting rule head hhead sample n (by rw [hstop])
  have hc : (run input C .uncapped accounting rule sample n).ledger.reviews head = n := by
    rw [hr]
    exact headReviewState_reviews input accounting head _ _ n
  have ha : (run input C .uncapped accounting rule sample n).halted = false := by
    rw [hr]
    exact headReviewState_active input accounting head _ _ n
  have hh : (run input C .uncapped accounting rule sample n).history =
      headReviewHistory input head (worldTapes input sample.2 head) n := by
    rw [hr]
    exact headReviewState_history input accounting head _ _ n
  cases extra with
  | zero => exact hc
  | succ extra =>
    rw [show n + (extra + 1) = (n + 1) + extra by omega]
    rcases nativeHead_exit_classification input C accounting rule hlegal head hhead sample n hstop with
      ⟨bit, hwrite⟩ | hstopOrAbandon
    · obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample n
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ m _ hp ha
      have hactual : rule sample.1 (run input C .uncapped accounting rule sample n).history = .write head bit := by
        rw [hh]
        exact hwrite
      have hnext := run_succ_of_step input C .uncapped accounting rule sample n next ha hs
      have hw : (run input C .uncapped accounting rule sample (n + 1)).ledger.written head = some bit := by
        rw [hnext]
        rw [hactual] at hs
        cases hs
        classical
        simp only [record, reportedWriteLedger]
        split_ifs <;> simp only [writeLedger, Function.update_self]
      have hreviews : (run input C .uncapped accounting rule sample (n + 1)).ledger.reviews head = n := by
        rw [hnext]
        rw [hactual] at hs
        cases hs
        simpa only [record, reportedWrite_reviews_unchanged] using hc
      rw [run_reviews_written_port input C .uncapped accounting rule hlegal sample (n + 1) extra head bit hw]
      exact hreviews
    · have hnext : (run input C .uncapped accounting rule sample (n + 1)).halted = true ∧
          (run input C .uncapped accounting rule sample (n + 1)).ledger.reviews head = n := by
        rcases hstopOrAbandon with ht | ht
        · have hs : Step input C .uncapped accounting (worldTapes input sample.2)
              (run input C .uncapped accounting rule sample n)
              (rule sample.1 (run input C .uncapped accounting rule sample n).history)
              (stopState (run input C .uncapped accounting rule sample n) false) := by
            rw [hh, ht]
            exact .stop _ ha
          rw [run_succ_of_step input C .uncapped accounting rule sample n _ ha hs]
          exact ⟨rfl, hc⟩
        · have hs : Step input C .uncapped accounting (worldTapes input sample.2)
              (run input C .uncapped accounting rule sample n)
              (rule sample.1 (run input C .uncapped accounting rule sample n).history)
              (stopState (run input C .uncapped accounting rule sample n) true) := by
            rw [hh, ht]
            exact .abandon _ ha
          rw [run_succ_of_step input C .uncapped accounting rule sample n _ ha hs]
          exact ⟨rfl, hc⟩
      rw [run_after_halt input C .uncapped accounting rule sample (n + 1) hnext.1 extra]
      exact hnext.2

/-- Exact stage accounting for every legal native head policy. It includes
non-MAP writes, abandonment, failing paths and infinite observation count;
no finite-ET or successful-path hypothesis is required. -/
theorem nativeHead_observationCharge_eq_stageBill (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (head : I.Stage) (hhead : head.val = 0)
    (sample : Seed × input.World) :
    (input.experiment head).observationCharge (headExitStop input head rule sample.1 (worldTapes input sample.2 head)) =
      runStageObservationBill input C .uncapped accounting rule head sample := by
  by_cases htop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = ⊤
  · rw [htop, BinaryExperiment.observationCharge_top]
    symm
    apply top_unique
    have hc (k : ℕ) : (run input C .uncapped accounting rule sample k).ledger.reviews head = k := by
      rw [run_eq_headReviewState input C accounting rule head hhead sample k (by rw [htop]; exact le_top)]
      exact headReviewState_reviews input accounting head _ _ k
    have hlo (k : ℕ) : ENNReal.ofReal ((input.experiment head).observationFee : ℝ) * k ≤
        runStageObservationBill input C .uncapped accounting rule head sample := by
      unfold runStageObservationBill
      have h := le_iSup (fun n => ENNReal.ofReal (input.fees.observation head : ℝ) *
        ((run input C .uncapped accounting rule sample n).ledger.reviews head : ℝ≥0∞)) k
      simpa only [hc k, ENat.toENNReal_coe, StatisticalInput.fees] using h
    have hs := iSup_le hlo
    rw [← ENNReal.mul_iSup, ENNReal.iSup_natCast] at hs
    have hfee : ENNReal.ofReal ((input.experiment head).observationFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (input.experiment head).observationFee_real_pos)
    simpa only [ENNReal.mul_top hfee] using hs
  · generalize hstop : headExitStop input head rule sample.1 (worldTapes input sample.2 head) = stop at htop ⊢
    lift stop to ℕ using htop with n
    rw [BinaryExperiment.observationCharge_nat]
    have hc := nativeHead_reviews_after_exit input C accounting rule hlegal head hhead sample n hstop 0
    simp only [Nat.add_zero] at hc
    apply le_antisymm
    · unfold runStageObservationBill
      have hlo := le_iSup (fun k => ENNReal.ofReal (input.fees.observation head : ℝ) *
        ((run input C .uncapped accounting rule sample k).ledger.reviews head : ℝ≥0∞)) n
      simpa only [hc, ENat.toENNReal_coe, StatisticalInput.fees] using hlo
    · unfold runStageObservationBill
      apply iSup_le
      intro k
      have hkn : (run input C .uncapped accounting rule sample k).ledger.reviews head ≤ n := by
        by_cases hk : k ≤ n
        · exact (run_reviews_mono input C .uncapped accounting rule hlegal sample head hk).trans hc.le
        · obtain ⟨extra, he⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
          rw [he, nativeHead_reviews_after_exit input C accounting rule hlegal head hhead sample n hstop extra]
      have hmul := mul_le_mul_right (ENat.toENNReal_mono hkn) (ENNReal.ofReal (input.fees.observation head : ℝ))
      simpa only [ENat.toENNReal_coe, StatisticalInput.fees] using hmul

end PDROC

