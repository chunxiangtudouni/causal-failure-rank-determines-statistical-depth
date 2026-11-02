module

public import PaperProofs.Paid.PDROC_OverlaySuccess_003
public import PaperProofs.Paid.PDROC_OverlaySuccess_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Actual Source SimSeed : Type*}

/-- Deterministic success assembly. The only error premise is a pointwise
statement about reports at this very finite prefix. -/
theorem overlaySuccess_prefix_success_of_error
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (herror : ∀ stage, s.ledger.written stage = some (!s.ledger.truth stage) →
      reportedWriteError (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed)
        simSeed s.history).shadow stage = some true)
    (hstop : VisibleEvent.stopped ∈ (overlayReplay draw mark
      (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow)
    (hresolved : ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved I
      (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow stage = true) :
    s.halted = true ∧ s.ledger.success C := by
  let virtual := (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow
  have hproj := overlayReplay_historyProjection draw mark
    (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history
  have hactualStop := (overlaySuccess_replay_stop draw mark
    (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).mp hstop
  obtain ⟨hlast, hhalt⟩ := overlaySuccess_prefix_stop_last input C hearly mode accounting rule seed truth tapes hp hactualStop
  have hall : allWritten s.ledger := by
    intro stage hw
    have hv := overlaySuccess_resolved_written virtual stage (hresolved stage)
    apply hv
    apply (hproj.2.1 stage).mp
    rwa [prefix_historyWritten input C mode accounting rule seed truth tapes hp stage]
  have hfinished := prefix_halted_allWritten_finished input C mode accounting rule seed truth tapes hp hhalt hall
  have habandoned := prefix_last_stopped_not_abandoned input C hearly mode accounting rule seed truth tapes hp hlast
  refine ⟨hhalt, (prefix_success_iff_physical input C mode accounting rule seed truth tapes hp).mpr ?_⟩
  refine ⟨hfinished, habandoned, fun stage => (finalOutput_correct_iff _ stage).mpr ?_⟩
  by_cases hc : s.ledger.written stage = some (s.ledger.truth stage)
  · exact Or.inl hc
  · obtain ⟨bit, hb⟩ := Option.ne_none_iff_exists.mp (hall stage)
    have hne : bit ≠ s.ledger.truth stage := by
      intro h
      exact hc (hb.symm.trans (congrArg some h))
    have hw : s.ledger.written stage = some (!s.ledger.truth stage) :=
      hb.symm.trans (congrArg some (Bool.eq_not_iff.mpr hne))
    obtain ⟨tool, he⟩ := overlaySuccess_resolved_error_exec virtual stage (hresolved stage) (herror stage hw)
    have hphysical := overlaySuccess_prefix_wrong_exec_physical input C hearly mode accounting
      rule seed truth tapes source oldSeed draw mark simSeed hp stage tool hw he
    change (stage, tool) ∈ (historyExecutions s.history).map (fun e => (e.1.stage, e.2)) at hphysical
    obtain ⟨pair, hm, hpstage⟩ := List.mem_map.mp hphysical
    rw [prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
    obtain ⟨execution, hem, heq⟩ := List.mem_map.mp hm
    apply Or.inr
    refine ⟨execution, hem, ?_⟩
    have hs := congrArg Prod.fst hpstage
    simpa only [← heq] using hs

end PDROC
