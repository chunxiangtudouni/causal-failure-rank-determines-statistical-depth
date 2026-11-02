module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_011
public import PaperProofs.Paid.PDROC_CalibratedRuntime_012
public import PaperProofs.Paid.PDROC_CalibratedRuntime_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters
open PDMenu

namespace PDROC.CalibratedRuntime

theorem calibratedStageTest_finite (P : Parameters) (level : ℕ) (seed : StageSeed P)
    (tape : P.experiment.Tape) :
    ∃ reviews : ℕ, (calibratedStageTest P level).rule.stop seed tape = reviews := by
  rw [calibratedStageTest_stop]
  have hbound := PDMenu.calibratedTest_stop_le P level (localCalibrationSeed P level seed, tape)
  have hfinite := ne_top_of_le_ne_top (ENat.natCast_ne_top P.certificate.Q) hbound
  obtain ⟨reviews, hr⟩ := ENat.ne_top_iff_exists.mp hfinite
  exact ⟨reviews, hr.symm⟩

/-- Strict actual remaining-stage induction. Every continuation is a
proved next physical first entry, and the malformed-level branch is the
literal original abandonment branch. No runtime/performance premise remains. -/
theorem entryRecords_induction (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    ∀ (n cursor clock : ℕ) (hfit : cursor + n = P.certificate.stages),
      FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) cursor clock sample →
        EntryRecords P table fee hfee C accounting sample cursor n clock hfit := by
  intro n
  induction n with
  | zero =>
    intro cursor clock hfit hentry
    exact entryRecords_zero P table fee hfee C hC.1.1 accounting sample cursor clock hfit hentry
  | succ n ih =>
    intro cursor clock hfit hentry
    let stage : P.sharedInstance.Stage := menuSuffixStage P.certificate.stages P.tools cursor (n + 1) hfit 0
    have hstage : stage.val = cursor := Nat.add_zero cursor
    have hnextfit : cursor + 1 + n = P.certificate.stages := by omega
    let k := P.tools - (run (P.input fee hfee) C .uncapped accounting (menuRule P table) sample clock).ledger.executions.length
    cases ha : (menuEntryAt table (n + 1) k).action with
    | finish => exact entryRecords_abandon P table fee hfee C hC.1.1 accounting sample cursor n clock hfit stage hstage hentry (.inr ha)
    | abandon => exact entryRecords_abandon P table fee hfee C hC.1.1 accounting sample cursor n clock hfit stage hstage hentry (.inl ha)
    | test level bad =>
      by_cases valid : level ≤ P.certificate.M
      · obtain ⟨reviews, hstop⟩ := calibratedStageTest_finite P level (sample.1.1 stage, sample.1.2 stage)
          (worldTapes (P.input fee hfee) sample.2 stage)
        by_cases hcorrect : (calibratedStageTest P level).rule.decision (sample.1.1 stage, sample.1.2 stage)
            (worldTapes (P.input fee hfee) sample.2 stage) = (P.input fee hfee).truthAt sample.2 stage
        · exact entryRecords_test_correct P table fee hfee C hC accounting sample cursor n clock hfit hnextfit
            stage hstage hentry level reviews bad valid ha hstop hcorrect
            (fun nextclock hnext => ih (cursor + 1) nextclock hnextfit hnext)
        · cases bad with
          | abandon =>
            exact entryRecords_test_abort P table fee hfee C hC accounting sample cursor n clock hfit
              stage hstage hentry level reviews .abandon valid ha hstop hcorrect (.inl rfl)
          | repair =>
            by_cases hz : k = 0
            · exact entryRecords_test_abort P table fee hfee C hC accounting sample cursor n clock hfit
                stage hstage hentry level reviews .repair valid ha hstop hcorrect (.inr hz)
            · exact entryRecords_test_repair P table fee hfee C hC accounting sample cursor n clock hfit hnextfit
                stage hstage hentry level reviews valid ha hstop hcorrect (Nat.pos_of_ne_zero hz)
                (fun nextclock hnext => ih (cursor + 1) nextclock hnextfit hnext)
      · exact entryRecords_invalid_level P table fee hfee C hC.1.1 accounting sample cursor n clock hfit
          stage hstage hentry level bad valid ha

theorem root_records (P : Parameters) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract P.sharedInstance) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedMenuSeed × (P.input fee hfee).World) :
    EntryRecords P table fee hfee C accounting sample 0 P.certificate.stages 0
      (Nat.zero_add P.certificate.stages) := by
  have hentry : FirstEntryAt (P.input fee hfee) C .uncapped accounting (menuRule P table) 0 0 sample := by
    refine ⟨rfl, ?_⟩
    intro j hj
    exact (Nat.not_lt_zero j hj).elim
  exact entryRecords_induction P table fee hfee C hC accounting sample
    P.certificate.stages 0 0 (Nat.zero_add P.certificate.stages) hentry

end PDROC.CalibratedRuntime
