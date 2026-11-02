module

public import PaperProofs.Retained.PRet_InformationStep_022
public import PaperProofs.Retained.PRet_PaymentPrefix_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetRunReplay023

open Common Common.Native PRetExactTerminal001 PRetInformationPackets006 PRetDelayedPolicy010
open PRetReplayInvariant016 PRetReplayConsequences017 PRetActualPacketReplay020
open PRetPaymentPrefix021 PRetActionOrigins019 PRetInformationStep022

variable {I : Instance}

theorem step_preserves {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) {n : ℕ} {target next : State I}
    (hprefix : Prefix input C .uncapped accounting (rule accounting source) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n target)
    (hi : ReplayInvariant input C mode accounting source sample target)
    (hs : Step input C .uncapped accounting (worldTapes input sample.2)
      target (rule accounting source sample.1 target.history) next) :
    ReplayInvariant input C mode accounting source sample next := by
  obtain ⟨packets, oldClock, hinfo, hreplay, hr, hw, hp⟩ := hi
  have hraw := raw_of_replay accounting source sample.1 target.history packets _ hinfo hreplay
  generalize haction : rule accounting source sample.1 target.history = action at hs
  have hc : action ≠ .abandon →
      candidate (publicStartup (run input C mode accounting source sample oldClock))
        (source sample.1 (run input C mode accounting source sample oldClock).history) target.history = action := by
    intro hne
    exact hraw.symm.trans (guarded_eq_raw accounting source sample.1 target.history action hne haction)
  cases hs with
  | review stage live port resources =>
    obtain ⟨ha, hselected⟩ := candidate_review _ _ _ stage (hc (by intro h; cases h))
    exact review_step input C mode accounting source hlegal sample _ _ stage packets oldClock
      hinfo hreplay hr hw hp ha hselected (.review _ stage live port resources)
  | write stage bit live port resources =>
    obtain ⟨ha, hselected⟩ := candidate_write _ _ _ stage bit (hc (by intro h; cases h))
    have htruth : target.ledger.truth = (run input C mode accounting source sample oldClock).ledger.truth :=
      (prefix_truth input C .uncapped accounting (rule accounting source) sample.1 _ _ hprefix).trans
        (run_truth input C mode accounting source hlegal sample oldClock).symm
    exact write_step input C hearly mode accounting source hlegal sample _ _ stage bit packets oldClock
      hinfo hreplay hr hw htruth hp ha hselected (.write _ stage bit live port resources)
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hcount : (historyExecutions target.history).length = target.ledger.executions.length := by
      rw [prefix_historyExecutions input C .uncapped accounting (rule accounting source) sample.1 _ _ hprefix,
        List.length_map]
    have hp' := candidate_execution_prefix _ _ target.history target.ledger.executions handle tool target.clock
      hcount hp (hc (by intro h; cases h))
    refine ⟨packets, oldClock, ?_, hreplay, hr, hw, ?_⟩
    · simpa only [record, informationTrace, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, informationEvent, List.append_nil] using hinfo
    · simpa only [record, executeLedger, publicStartup] using hp'
  | allocate handle tool active valid compatible unused unallocated window resources =>
    refine ⟨packets, oldClock, ?_, hreplay, hr, hw, hp⟩
    simpa only [record, informationTrace, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, informationEvent, List.append_nil] using hinfo
  | advance stage live written resources =>
    refine ⟨packets, oldClock, ?_, hreplay, hr, hw, hp⟩
    simpa only [record, informationTrace, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, informationEvent, List.append_nil] using hinfo
  | stop active =>
    refine ⟨packets, oldClock, ?_, hreplay, hr, hw, hp⟩
    simpa only [stopState, Bool.false_eq_true, ↓reduceIte, informationTrace,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, informationEvent,
      List.append_nil] using hinfo
  | abandon active =>
    refine ⟨packets, oldClock, ?_, hreplay, hr, hw, hp⟩
    simpa only [stopState, ↓reduceIte, informationTrace,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, informationEvent,
      List.append_nil] using hinfo

theorem prefix_replayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) {n : ℕ} {target : State I}
    (hp : Prefix input C .uncapped accounting (rule accounting source) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n target) :
    ReplayInvariant input C mode accounting source sample target := by
  induction hp with
  | initial => exact replayInvariant_initial input C mode accounting source hlegal sample
  | next earlier step ih => exact step_preserves input C hearly mode accounting source hlegal sample earlier ih step

theorem run_replayInvariant {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (n : ℕ) :
    ReplayInvariant input C mode accounting source sample
      (run input C .uncapped accounting (rule accounting source) sample n) := by
  have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htarget sample n
  exact prefix_replayInvariant input C hretained.1 mode accounting source hlegal sample hp

end PaperProofs.Retained.PRetRunReplay023
