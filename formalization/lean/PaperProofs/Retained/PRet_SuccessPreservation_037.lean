module

public import PaperProofs.Retained.PRet_TerminalCompletion_035
public import PaperProofs.Retained.PRet_HaltedPairs_036
public import PaperProofs.Retained.PRet_BarrierSource_030

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetSuccessPreservation037

open Common Common.Native PRetExactTerminal001 PRetDelayedPolicy010 PRetInformationPackets006
open PRetReplayInvariant016 PRetReplayConsequences017 PRetRunReplay023 PRetPathwiseDomination024
open PRetBarrierArrival029 PRetBarrierSource030 PRetSourceSuccess027 PRetTerminalCompletion035
open PRetHaltedPairs036 PRetFiniteSourceHalt025

variable {I : Instance}

theorem success_preserved {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample) :
    runSuccess input C .uncapped accounting (rule accounting source) sample ∧
    eventualPairs input C .uncapped accounting (rule accounting source) sample =
      eventualPairs input C mode accounting source sample ∧
    ∀ n, ∃ newClock,
      (informationTrace (run input C mode accounting source sample n).history).IsPrefix
        (informationTrace (run input C .uncapped accounting (rule accounting source) sample newClock).history) := by
  obtain ⟨barrier, hc, ha, hcommit, hexec⟩ := clean_barrier_arrival input C hretained mode accounting source hlegal sample hsuccess
  obtain ⟨packets, oldClock, hinfo, hreplay, _, hwritten, _⟩ :=
    run_replayInvariant input C hretained mode accounting source hlegal sample barrier
  have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htarget sample barrier
  have hhaltSource := barrier_source_halted input C mode accounting source hlegal sample hp hc packets oldClock hreplay hwritten
  have hgoodSource := halted_source_success input C mode accounting source sample hsuccess oldClock hhaltSource
  have hshadow : shadow accounting source sample.1
      (run input C .uncapped accounting (rule accounting source) sample barrier).history =
        some (publicStartup (run input C mode accounting source sample oldClock)) := by
    unfold shadow
    rw [hinfo, parse_packets]
    exact hreplay
  have htruth := (run_truth input C .uncapped accounting (rule accounting source) htarget sample barrier).trans
    (run_truth input C mode accounting source hlegal sample oldClock).symm
  obtain ⟨last, hh, hs, hpairs, hshadowFinal⟩ := complete_terminal_source input C hretained mode accounting source hlegal sample
    oldClock barrier hhaltSource hgoodSource hc ha hshadow htruth hwritten hcommit hexec
  refine ⟨⟨last, hh, hs⟩, ?_, ?_⟩
  · rw [eventualPairs_of_halted input C .uncapped accounting (rule accounting source) htarget sample last hh,
      eventualPairs_of_halted input C mode accounting source hlegal sample oldClock hhaltSource, hpairs]
  · have hfinalInfo : informationTrace (run input C mode accounting source sample oldClock).history =
        informationTrace (run input C .uncapped accounting (rule accounting source) sample last).history := by
      obtain ⟨_, _, hi⟩ := shadow_run input C hretained mode accounting source hlegal sample last
      simpa only [shadowHistory, hshadowFinal, extractHistory, publicStartup] using hi
    intro n
    refine ⟨last, ?_⟩
    rw [← hfinalInfo]
    exact source_information_prefix_of_halted input C mode accounting source hlegal sample oldClock n hhaltSource

end PaperProofs.Retained.PRetSuccessPreservation037
