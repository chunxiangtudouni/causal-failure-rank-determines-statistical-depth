module

public import PaperProofs.Retained.PRet_BarrierArrival_029

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetBarrierSource030

open Common Common.Native PRetDelayedPolicy010 PRetReplayInvariant016
open PRetInformationPackets006 PRetPastWritten015 PRetSourceSuccess027 PRetPaymentPrefix021

variable {I : Instance}

/-- At an actual terminal cursor every source cache is itself halted:
otherwise its next saturated information action would require a fresh
ordinary write port, contrary to the genuinely written target ledger. -/
theorem barrier_source_halted {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hlegal : LegalRule input C mode accounting source) (sample : Seed × input.World)
    {n : ℕ} {target : State I}
    (hp : Prefix input C .uncapped accounting (rule accounting source) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n target)
    (hcursor : target.cursor = I.stageCount) (packets : List (Packet I)) (oldClock : ℕ)
    (hreplay : replay accounting source sample.1 packets =
      some (publicStartup (run input C mode accounting source sample oldClock)))
    (hwritten : target.ledger.written = (run input C mode accounting source sample oldClock).ledger.written) :
    (run input C mode accounting source sample oldClock).halted = true := by
  by_contra hh
  have ha := Bool.eq_false_iff.mpr hh
  have hall : allWritten (run input C mode accounting source sample oldClock).ledger := by
    intro stage
    rw [← hwritten]
    exact prefix_past_written input C .uncapped accounting (rule accounting source) sample.1 _ _ hp stage
      (by rw [hcursor]; exact stage.isLt)
  obtain ⟨sourceClock, _, hsourcePrefix⟩ := run_has_prefix input C mode accounting source hlegal sample oldClock
  obtain ⟨stage, hreview | ⟨bit, hwrite⟩⟩ :=
    active_replay_information input C mode accounting source hlegal sample packets oldClock hreplay ha
  · obtain ⟨next, hs⟩ := hlegal sample.1 _ _ sourceClock _ hsourcePrefix ha
    rw [hreview] at hs
    cases hs with
    | review _ live port resources => exact hall stage port
  · obtain ⟨next, hs⟩ := hlegal sample.1 _ _ sourceClock _ hsourcePrefix ha
    rw [hwrite] at hs
    cases hs with
    | write _ _ live port resources => exact hall stage port

theorem successful_barrier_cache {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (hsuccess : runSuccess input C mode accounting source sample)
    (n : ℕ) (hcursor : (run input C .uncapped accounting (rule accounting source) sample n).cursor = I.stageCount) :
    ∃ oldClock,
      shadow accounting source sample.1 (run input C .uncapped accounting (rule accounting source) sample n).history =
        some (publicStartup (run input C mode accounting source sample oldClock)) ∧
      (run input C mode accounting source sample oldClock).halted = true ∧
      (run input C mode accounting source sample oldClock).ledger.success C := by
  obtain ⟨packets, oldClock, hinfo, hreplay, _, hwritten, _⟩ :=
    PRetRunReplay023.run_replayInvariant input C hretained mode accounting source hlegal sample n
  have htarget := PRetRetainedGuard007.guarded_legal input C hretained accounting (raw accounting source)
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (rule accounting source) htarget sample n
  have hhalt := barrier_source_halted input C mode accounting source hlegal sample hp hcursor packets oldClock hreplay hwritten
  refine ⟨oldClock, ?_, hhalt, halted_source_success input C mode accounting source sample hsuccess oldClock hhalt⟩
  unfold shadow
  rw [hinfo, parse_packets]
  exact hreplay

end PaperProofs.Retained.PRetBarrierSource030
