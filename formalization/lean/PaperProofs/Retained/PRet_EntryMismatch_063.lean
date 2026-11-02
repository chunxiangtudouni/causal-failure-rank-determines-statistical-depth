module

public import PaperProofs.Retained.PRet_EntryRun_057
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryMismatch063

open Common Common.Native PRetEntryInvariant050 PRetEntryRun057

variable {I : Instance}

theorem run_mismatches_subset_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (last : ℕ) (hh : (run input C mode accounting source sample last).halted = true) (n : ℕ) :
    ordinaryMismatches (run input C mode accounting source sample n).ledger ⊆
      ordinaryMismatches (run input C mode accounting source sample last).ledger := by
  intro stage hstage
  by_cases hle : n ≤ last
  · have hw := (mem_ordinaryMismatches _ stage).mp hstage
    have hpersist := run_written_some_after input C mode accounting source hlegal sample n (last - n)
      stage _ hw
    rw [Nat.add_sub_of_le hle, run_truth input C mode accounting source hlegal sample n] at hpersist
    apply (mem_ordinaryMismatches _ stage).mpr
    rw [run_truth input C mode accounting source hlegal sample last]
    exact hpersist
  · have hle' : last ≤ n := by omega
    have heq := run_after_halt input C mode accounting source sample last hh (n - last)
    rw [Nat.add_sub_of_le hle'] at heq
    rw [heq] at hstage
    exact hstage

/-- Actual fresh ordinary errors map to actual full-source errors. The
pullback is applied to written values AND genuine hidden truths, not to a
success-conditioned virtual trace. -/
theorem liftedErrors_subset_source {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (first oldClock : ℕ) (target : State (I.freshSuffix first))
    (hw : target.ledger.written = (fun stage =>
      (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage)))
    (ht : target.ledger.truth = (input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2)) :
    liftedErrors I first target.ledger ⊆ ordinaryMismatches (run input C mode accounting source sample oldClock).ledger := by
  intro original horiginal
  obtain ⟨stage, hstage, rfl⟩ := Finset.mem_image.mp horiginal
  apply (mem_ordinaryMismatches _ _).mpr
  have hwrong := (mem_ordinaryMismatches _ stage).mp hstage
  rw [hw, ht] at hwrong
  change (run input C mode accounting source sample oldClock).ledger.written (I.freshStageLift first stage) =
    some (!((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2) stage)) at hwrong
  rw [restrictFreshWorld_truth input first sample.2 stage] at hwrong
  rw [run_truth input C mode accounting source hlegal sample oldClock]
  exact hwrong

/-- Joint old-H matching transfer to every real extracted prefix. The
terminal native matching is used only as a witness; no fresh/native success
identification or available-tool policy restriction is inserted. -/
theorem joint_errors_matchable {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample) (old : Finset I.Stage)
    (hold : old ⊆ ordinaryMismatches (run input C mode accounting source sample start).ledger)
    (last : ℕ) (hh : (run input C mode accounting source sample last).halted = true)
    (hm : Matchable I (ordinaryMismatches (run input C mode accounting source sample last).ledger)) (n : ℕ) :
    Matchable I (old ∪ liftedErrors I first
      (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
        (sample.1, input.restrictFreshWorld first sample.2) n).ledger) := by
  have htarget := (PRetFreshExtractionPolicy047.policy input first accounting source hsource
    (publicStartup (run input C mode accounting source sample start))).legal
  have ht := run_truth (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) _ htarget (sample.1, input.restrictFreshWorld first sample.2) n
  obtain ⟨_, oldClock, _, _, _, _, hw⟩ := run_entryInvariant input C hearly mode accounting source hsource hlegal
    sample first start hentry n
  apply hm.subset
  apply Finset.union_subset
  · exact hold.trans (run_mismatches_subset_halted input C mode accounting source hlegal sample last hh start)
  · exact (liftedErrors_subset_source input C mode accounting source hlegal sample first oldClock _ hw ht).trans
      (run_mismatches_subset_halted input C mode accounting source hlegal sample last hh oldClock)

end PaperProofs.Retained.PRetEntryMismatch063



