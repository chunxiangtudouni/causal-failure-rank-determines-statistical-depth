module

public import PaperProofs.Paid.PDROC_DirectEntry_001
public import PaperProofs.Paid.PDROC_LocalRecord_011

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

private theorem direct_reportedWrite_reviews {I : Instance} (C : Contract I)
    (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

theorem firstEntry_direct_reviews_after_exit (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting rule stage.val start sample)
    (n : ℕ)
    (hstop : headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
        (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞)) (extra : ℕ) :
    (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n + extra)).ledger.reviews stage = n := by
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hfee) C.val .uncapped accounting rule hl sample stage.val start he
  have hr := run_eq_entryReviewState_before_directExit P fee hfee C.val accounting rule sample start stage
    ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 n (by rw [hstop])
  have hc : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).ledger.reviews stage = n := by
    rw [hr, entryReviewState_reviews, (hunborn stage le_rfl).2, zero_add]
  have hactive : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).halted = false := by
    rw [hr]
    exact entryReviewState_active _ _ _ _ _ n ha
  have hcursor : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).cursor = stage.val := by
    rw [hr, entryReviewState_cursor]
    exact he.1
  have hwritten : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).ledger.written stage = none := by
    rw [hr, entryReviewState_written]
    exact (hunborn stage le_rfl).1
  have hnot : rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history ≠ .review stage := by
    rw [hr, entryReviewState_history]
    exact headExitStop_hits (P.input fee hfee) stage (simulatorPrewriteRule P rule)
      (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
      (worldTapes (P.input fee hfee) sample.2 stage) n hstop
  have hcases := currentPayment_unwritten_action_cases (P.input fee hfee) C.val C.property .uncapped accounting
    rule hl sample (start + n) stage hactive hcursor hwritten
  cases extra with
  | zero => exact hc
  | succ extra =>
    rw [show start + n + (extra + 1) = (start + n + 1) + extra by omega]
    rcases hcases with hreview | ⟨bit, hwrite⟩ | hstop' | habandon
    · exact (hnot hreview).elim
    · obtain ⟨m, _hm, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting rule hl sample (start + n)
      obtain ⟨next, hs⟩ := hl sample.1 _ _ m _ hp hactive
      have hnext := run_succ_of_step (P.input fee hfee) C.val .uncapped accounting rule sample (start + n) next hactive hs
      have hw : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n + 1)).ledger.written stage = some bit := by
        rw [hnext]
        rw [hwrite] at hs
        cases hs
        classical
        simp only [record, reportedWriteLedger]
        split_ifs <;> simp only [writeLedger, Function.update_self]
      have hrev : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n + 1)).ledger.reviews stage = n := by
        rw [hnext]
        rw [hwrite] at hs
        cases hs
        simpa only [record, direct_reportedWrite_reviews] using hc
      rw [run_reviews_written_port (P.input fee hfee) C.val .uncapped accounting rule hl sample (start + n + 1) extra stage bit hw]
      exact hrev
    · have hs : Step (P.input fee hfee) C.val .uncapped accounting (worldTapes (P.input fee hfee) sample.2)
          (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n))
          (rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history)
          (stopState (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)) false) := by
        rw [hstop']; exact .stop _ hactive
      have hnext := run_succ_of_step (P.input fee hfee) C.val .uncapped accounting rule sample (start + n) _ hactive hs
      rw [run_after_halt (P.input fee hfee) C.val .uncapped accounting rule sample (start + n + 1)
        (by rw [hnext]; rfl) extra, hnext]
      exact hc
    · have hs : Step (P.input fee hfee) C.val .uncapped accounting (worldTapes (P.input fee hfee) sample.2)
          (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n))
          (rule sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)).history)
          (stopState (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + n)) true) := by
        rw [habandon]; exact .abandon _ hactive
      have hnext := run_succ_of_step (P.input fee hfee) C.val .uncapped accounting rule sample (start + n) _ hactive hs
      rw [run_after_halt (P.input fee hfee) C.val .uncapped accounting rule sample (start + n + 1)
        (by rw [hnext]; rfl) extra, hnext]
      exact hc

/-- Exact actual-stage charge for the concrete direct prewrite sampler used
by simulatorDrawAt, including abandonment, every failure, and infinite stops. -/
theorem firstEntry_direct_observationCharge_eq_stageBill (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (rule : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting rule)
    (sample : Seed × (P.input fee hfee).World) (start : ℕ) (stage : P.sharedInstance.Stage)
    (he : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting rule stage.val start sample) :
    ((P.input fee hfee).experiment stage).observationCharge
      (headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
        (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
          (worldTapes (P.input fee hfee) sample.2 stage)) =
      runStageObservationBill (P.input fee hfee) C.val .uncapped accounting rule stage sample := by
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn (P.input fee hfee) C.val .uncapped accounting rule hl sample stage.val start he
  let stop := headExitStop (P.input fee hfee) stage (simulatorPrewriteRule P rule)
    (sample.1, (run (P.input fee hfee) C.val .uncapped accounting rule sample start).history)
      (worldTapes (P.input fee hfee) sample.2 stage)
  by_cases htop : stop = ⊤
  · change ((P.input fee hfee).experiment stage).observationCharge stop = _
    rw [htop, PaperProofs.Statistics.BinaryExperiment.observationCharge_top]
    symm
    apply top_unique
    have hc (k : ℕ) : (run (P.input fee hfee) C.val .uncapped accounting rule sample (start + k)).ledger.reviews stage = k := by
      rw [run_eq_entryReviewState_before_directExit P fee hfee C.val accounting rule sample start stage
        ha he.1 (hunborn stage le_rfl).1 (hunborn stage le_rfl).2 k (by change (k : ℕ∞) ≤ stop; rw [htop]; exact le_top),
        entryReviewState_reviews, (hunborn stage le_rfl).2, zero_add]
    have hlo (k : ℕ) : ENNReal.ofReal (P.reviewFee : ℝ) * k ≤
        runStageObservationBill (P.input fee hfee) C.val .uncapped accounting rule stage sample := by
      unfold runStageObservationBill
      have h := le_iSup (fun n => ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ) *
        ((run (P.input fee hfee) C.val .uncapped accounting rule sample n).ledger.reviews stage : ℝ≥0∞)) (start + k)
      have hfeeEq : (P.input fee hfee).fees.observation stage = P.reviewFee := rfl
      simpa only [hc k, ENat.toENNReal_coe, hfeeEq] using h
    have hs := iSup_le hlo
    rw [← ENNReal.mul_iSup, ENNReal.iSup_natCast] at hs
    have hfee0 : ENNReal.ofReal (P.reviewFee : ℝ) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (show 0 < (P.reviewFee : ℝ) by exact_mod_cast P.reviewFee_pos))
    simpa only [ENNReal.mul_top hfee0] using hs
  · change ((P.input fee hfee).experiment stage).observationCharge stop = _
    generalize hstop : stop = value at htop ⊢
    lift value to ℕ using htop with n
    rw [PaperProofs.Statistics.BinaryExperiment.observationCharge_nat]
    have hc := firstEntry_direct_reviews_after_exit P fee hfee C accounting rule hl sample start stage he n hstop 0
    simp only [Nat.add_zero] at hc
    apply le_antisymm
    · unfold runStageObservationBill
      have hlo := le_iSup (fun k => ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ) *
        ((run (P.input fee hfee) C.val .uncapped accounting rule sample k).ledger.reviews stage : ℝ≥0∞)) (start + n)
      simpa only [hc, ENat.toENNReal_coe, StatisticalInput.fees] using hlo
    · unfold runStageObservationBill
      apply iSup_le
      intro k
      have hkn : (run (P.input fee hfee) C.val .uncapped accounting rule sample k).ledger.reviews stage ≤ n := by
        by_cases hk : k ≤ start + n
        · exact (run_reviews_mono (P.input fee hfee) C.val .uncapped accounting rule hl sample stage hk).trans hc.le
        · obtain ⟨extra, hk⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hk)
          rw [hk, firstEntry_direct_reviews_after_exit P fee hfee C accounting rule hl sample start stage he n hstop extra]
      have hmul := mul_le_mul_right (ENat.toENNReal_mono hkn)
        (ENNReal.ofReal ((P.input fee hfee).fees.observation stage : ℝ))
      simpa only [ENat.toENNReal_coe, StatisticalInput.fees] using hmul

end PDROC
