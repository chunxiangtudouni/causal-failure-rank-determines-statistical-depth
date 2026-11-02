module

public import PaperProofs.Retained.PRet_EntryWriteStep_056
public import PaperProofs.Retained.PRet_ExtractionActions_051

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryRun057

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045
open PRetEntryInvariant050 PRetEntryPacketInvariant054 PRetExtractionActions051

variable {I : Instance}

theorem step_preserves {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ) (startup : Startup I)
    {n : ℕ} {target next : State (I.freshSuffix first)}
    (hprefix : Prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (PRetFreshExtractionPolicy047.rule first accounting source startup)
      sample.1 ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) n target)
    (hi : EntryInvariant input C mode accounting source sample first start startup target)
    (hs : Step (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) target
      (PRetFreshExtractionPolicy047.rule first accounting source startup sample.1 target.history) next) :
    EntryInvariant input C mode accounting source sample first start startup next := by
  obtain ⟨packets, oldClock, hclock, hinfo, hreplay, hr, hw⟩ := hi
  have hshadow : shadowFrom first accounting source startup sample.1 target.history =
      some (publicStartup (run input C mode accounting source sample oldClock)) := by
    unfold shadowFrom
    rw [hinfo, parse_packets]
    exact hreplay
  have hraw := PRetFreshExtractionPolicy047.raw_of_shadow first accounting source startup _ sample.1 target.history hshadow
  change PRetFreshExtractionPolicy047.raw first accounting source startup sample.1 target.history =
    PRetFreshExtractionPolicy047.candidate first (publicStartup (run input C mode accounting source sample oldClock))
      (source sample.1 (run input C mode accounting source sample oldClock).history) target.history at hraw
  generalize haction : PRetFreshExtractionPolicy047.rule first accounting source startup sample.1 target.history = action at hs
  have hc : action ≠ .abandon →
      PRetFreshExtractionPolicy047.candidate first (publicStartup (run input C mode accounting source sample oldClock))
        (source sample.1 (run input C mode accounting source sample oldClock).history) target.history = action := by
    intro hne
    exact hraw.symm.trans (guarded_eq_raw first accounting source startup sample.1 target.history action hne haction)
  have hbase : EntryInvariant input C mode accounting source sample first start startup target :=
    ⟨packets, oldClock, hclock, hinfo, hreplay, hr, hw⟩
  cases hs with
  | review stage live port resources =>
    obtain ⟨ha, hselected⟩ := candidate_review first _ _ _ stage (hc (by intro h; cases h))
    exact PRetEntryReviewStep055.review_step input C mode accounting source hlegal sample first start oldClock startup
      _ _ stage packets hclock hinfo hreplay hr hw ha hselected (.review _ stage live port resources)
  | write stage bit live port resources =>
    obtain ⟨ha, hselected⟩ := candidate_write first _ _ _ stage bit (hc (by intro h; cases h))
    have htruth : target.ledger.truth stage =
        (run input C mode accounting source sample oldClock).ledger.truth (I.freshStageLift first stage) := by
      rw [prefix_truth (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) (PRetFreshExtractionPolicy047.rule first accounting source startup)
        sample.1 _ _ hprefix, run_truth input C mode accounting source hlegal sample oldClock]
      exact restrictFreshWorld_truth input first sample.2 stage
    exact PRetEntryWriteStep056.write_step input C hearly mode accounting source hlegal sample first start oldClock startup
      _ _ stage bit packets hclock hinfo hreplay hr hw htruth ha hselected (.write _ stage bit live port resources)
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have hn := rule_no_correction first accounting source startup sample.1 target.history
    rw [haction] at hn
    cases hn
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hn := rule_no_correction first accounting source startup sample.1 target.history
    rw [haction] at hn
    cases hn
  | advance stage live written resources =>
    apply entryInvariant_frame input C mode accounting source sample first start startup target _ hbase
    · simp only [record, informationTrace, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, informationEvent, List.append_nil]
    · rfl
    · rfl
  | stop active =>
    apply entryInvariant_frame input C mode accounting source sample first start startup target _ hbase
    · simp only [stopState, Bool.false_eq_true, ↓reduceIte, informationTrace,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, informationEvent, List.append_nil]
    · rfl
    · rfl
  | abandon active =>
    apply entryInvariant_frame input C mode accounting source sample first start startup target _ hbase
    · simp only [stopState, ↓reduceIte, informationTrace, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, informationEvent, List.append_nil]
    · rfl
    · rfl

theorem prefix_entryInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    {n : ℕ} {target : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) (PRetFreshExtractionPolicy047.rule first accounting source
        (publicStartup (run input C mode accounting source sample start)))
      sample.1 ((input.freshSuffix first).truthAt (input.restrictFreshWorld first sample.2))
      (worldTapes (input.freshSuffix first) (input.restrictFreshWorld first sample.2)) n target) :
    EntryInvariant input C mode accounting source sample first start
      (publicStartup (run input C mode accounting source sample start)) target := by
  induction hp with
  | initial => exact entryInvariant_initial input C mode accounting source hlegal sample first start hentry
  | next earlier step ih =>
    exact step_preserves input C hearly mode accounting source hlegal sample first start _ earlier ih step

theorem run_entryInvariant {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample) (n : ℕ) :
    EntryInvariant input C mode accounting source sample first start
      (publicStartup (run input C mode accounting source sample start))
      (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first))
        (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
        (sample.1, input.restrictFreshWorld first sample.2) n) := by
  have htarget := (PRetFreshExtractionPolicy047.policy input first accounting source hsource
    (publicStartup (run input C mode accounting source sample start))).legal
  obtain ⟨_, _, hp⟩ := run_has_prefix (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first))
    (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
    htarget (sample.1, input.restrictFreshWorld first sample.2) n
  exact prefix_entryInvariant input C hearly mode accounting source hlegal sample first start hentry hp

end PaperProofs.Retained.PRetEntryRun057
