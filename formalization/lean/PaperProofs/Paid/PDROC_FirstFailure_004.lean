module

public import PaperProofs.Paid.PDROC_FirstFailure_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

/-- Halting is already public. A detector need only classify active states. -/
def activeDetector (detect : List (VisibleEvent I) → Bool) (history : List (VisibleEvent I)) : Bool :=
  (!historyHalted history) && detect history

theorem historyHalted_run (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World) (n : ℕ) :
    historyHalted (run input C mode accounting source sample n).history =
      (run input C mode accounting source sample n).halted := by
  obtain ⟨k, _, hp⟩ := run_has_prefix input C mode accounting source hlegal sample n
  exact prefix_historyHalted input C mode accounting source sample.1 _ _ hp

theorem firstFailureDomination_of_active_detector [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (detect : List (VisibleEvent I) → Bool) (source : Policy input C .uncapped accounting Seed)
    (hdetect : ∀ (sample : Seed × input.World) (n : ℕ),
      (run input C .uncapped accounting source.rule sample n).halted = false →
        (detect (run input C .uncapped accounting source.rule sample n).history = true ↔
          PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting source.rule sample n))) :
    FirstFailureDomination input C .uncapped accounting source
      (detectedStopPolicy input C .uncapped accounting (activeDetector detect) source) := by
  have hfalse (sample : Seed × input.World) (n : ℕ)
      (hn : ¬ PermanentlyFailed input C accounting sample.2
        (run input C .uncapped accounting source.rule sample n)) :
      activeDetector detect (run input C .uncapped accounting source.rule sample n).history = false := by
    rw [activeDetector, historyHalted_run input C .uncapped accounting source.rule source.legal sample n]
    by_cases hh : (run input C .uncapped accounting source.rule sample n).halted = true
    · simp only [hh, Bool.not_true, Bool.false_and]
    · have ha := Bool.eq_false_iff.mpr hh
      have hd : detect (run input C .uncapped accounting source.rule sample n).history = false :=
        Bool.eq_false_iff.mpr (fun hd => hn ((hdetect sample n ha).mp hd))
      simp only [ha, hd, Bool.not_false, Bool.true_and]
  have hsound (sample : Seed × input.World) (n : ℕ)
      (hd : activeDetector detect (run input C .uncapped accounting source.rule sample n).history = true) :
      PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting source.rule sample n) := by
    rw [activeDetector, historyHalted_run input C .uncapped accounting source.rule source.legal sample n] at hd
    have hand : (run input C .uncapped accounting source.rule sample n).halted = false ∧
        detect (run input C .uncapped accounting source.rule sample n).history = true := by
      simpa only [Bool.and_eq_true_eq_eq_true_and_eq_true, Bool.not_eq_true_eq_eq_false] using hd
    exact (hdetect sample n hand.1).mp hand.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact detectedStop_runSuccess_iff_of_sound input C accounting (activeDetector detect) source.rule source.legal hsound
  · intro sample n hbefore
    exact detectedStop_run_eq_before input C .uncapped accounting (activeDetector detect) source.rule sample n
      (fun k hk => hfalse sample k (hbefore k hk))
  · intro sample n hn hbefore extra
    have hbefore' : ∀ k < n, activeDetector detect (run input C .uncapped accounting source.rule sample k).history = false :=
      fun k hk => hfalse sample k (hbefore k hk)
    by_cases hh : (run input C .uncapped accounting source.rule sample n).halted = true
    · have heq := detectedStop_run_eq_before input C .uncapped accounting (activeDetector detect) source.rule sample n hbefore'
      have hhalt : (run input C .uncapped accounting (activeDetector detect |> fun d => detectedStopRule d source.rule) sample n).halted = true :=
        heq.symm ▸ hh
      have hrun := run_after_halt input C .uncapped accounting (detectedStopRule (activeDetector detect) source.rule) sample n hhalt (1 + extra)
      simpa only [Nat.add_assoc, heq, failureStop, hh, ↓reduceIte, detectedStopPolicy] using hrun
    · have ha := Bool.eq_false_iff.mpr hh
      have hd : activeDetector detect (run input C .uncapped accounting source.rule sample n).history = true := by
        simp only [activeDetector, historyHalted_run input C .uncapped accounting source.rule source.legal sample n,
          ha, Bool.not_false, Bool.true_and]
        exact (hdetect sample n ha).mpr hn
      exact detectedStop_run_after_first input C .uncapped accounting (activeDetector detect) source.rule sample n hbefore' hd extra
  · intro sample
    exact ⟨detectedStop_runObservationBill_le input C .uncapped accounting (activeDetector detect) source.rule sample,
      detectedStop_runActualBill_le input C .uncapped accounting (activeDetector detect) source.rule sample⟩

theorem firstFailureDomination_of_active_detector_any_mode [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (detect : List (VisibleEvent I) → Bool)
    (source : Policy input C mode accounting Seed)
    (hdetect : ∀ (sample : Seed × input.World) (n : ℕ),
      (run input C mode accounting source.rule sample n).halted = false →
        (detect (run input C mode accounting source.rule sample n).history = true ↔
          PermanentlyFailed input C accounting sample.2 (run input C mode accounting source.rule sample n))) :
    FirstFailureDomination input C mode accounting source
      (detectedStopPolicy input C .uncapped accounting (activeDetector detect)
        (uncappedSourcePolicy input C mode accounting source)) := by
  have hg := firstFailureDomination_of_active_detector input C accounting detect
    (uncappedSourcePolicy input C mode accounting source)
    (fun sample n => by simpa only [uncappedSourcePolicy_run] using hdetect sample n)
  simpa only [FirstFailureDomination, runSuccess, runObservationBill, runActualBill,
    uncappedSourcePolicy_run] using hg

end PDROC


