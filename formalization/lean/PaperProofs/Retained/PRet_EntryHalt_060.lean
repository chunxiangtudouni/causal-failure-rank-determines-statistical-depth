module

public import PaperProofs.Retained.PRet_EntryRun_057
public import PaperProofs.Retained.PRet_LiftedPacketFrames_052
public import PaperProofs.Retained.PRet_FiniteSourceHalt_025

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetEntryHalt060

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045
open PRetEntryInvariant050 PRetEntryRun057 PRetLiftedPacketFrames052
open PRetFiniteSourceHalt025 PRetAdministrativeClock003

variable {I : Instance}

theorem information_bound {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (last : ℕ) (hh : (run input C mode accounting source sample last).halted = true) (n : ℕ) :
    (informationTrace (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
      (sample.1, input.restrictFreshWorld first sample.2) n).history).length ≤
      (informationTrace (run input C mode accounting source sample last).history).length := by
  obtain ⟨packets, oldClock, _, hinfo, hreplay, _, _⟩ :=
    run_entryInvariant input C hearly mode accounting source hsource hlegal sample first start hentry n
  have hi := replayFrom_information accounting source sample.1
    (publicStartup (run input C mode accounting source sample start)) _ _ hreplay
  have hlen := congrArg List.length hi
  change (informationTrace (run input C mode accounting source sample oldClock).history).length =
    (informationTrace (publicStartup (run input C mode accounting source sample start)).history ++
      (packets.map (liftPacket first)).flatMap Packet.events).length at hlen
  rw [List.length_append, lifted_packets_information_length] at hlen
  rw [hinfo]
  have hprefix := (source_information_prefix_of_halted input C mode accounting source hlegal sample last oldClock hh).length_le
  omega

/-- Finite source halt yields finite actual extracted halt. The statement
intentionally does not yet assert matching or successful completion. -/
theorem halted_of_source_halted {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hsource : MeasurableRule source) (hlegal : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (first start : ℕ)
    (hentry : FirstEntryAt input C mode accounting source first start sample)
    (last : ℕ) (hh : (run input C mode accounting source sample last).halted = true) :
    (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first))
      (PRetFreshExtractionPolicy047.rule first accounting source (publicStartup (run input C mode accounting source sample start)))
      (sample.1, input.restrictFreshWorld first sample.2)
      ((informationTrace (run input C mode accounting source sample last).history).length +
        (I.freshSuffix first).stageCount + 2 * (I.freshSuffix first).toolCount + 2)).halted = true := by
  let targetRule := PRetFreshExtractionPolicy047.rule first accounting source
    (publicStartup (run input C mode accounting source sample start))
  let bound := (informationTrace (run input C mode accounting source sample last).history).length +
    (I.freshSuffix first).stageCount + 2 * (I.freshSuffix first).toolCount + 2
  have htarget := (PRetFreshExtractionPolicy047.policy input first accounting source hsource
    (publicStartup (run input C mode accounting source sample start))).legal
  by_contra hn
  have ha : (run (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule
      (sample.1, input.restrictFreshWorld first sample.2) bound).halted = false := Bool.eq_false_iff.mpr hn
  have hp := run_prefix_of_active (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule htarget (sample.1, input.restrictFreshWorld first sample.2) bound ha
  have hc := prefix_clock_le_information (input.freshSuffix first) (freshContract (I.freshSuffix first)) rfl .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule sample.1 _ _ hp
  have hi := information_bound input C hearly mode accounting source hsource hlegal sample first start hentry last hh bound
  dsimp only [bound, targetRule] at hc hi
  omega

end PaperProofs.Retained.PRetEntryHalt060

