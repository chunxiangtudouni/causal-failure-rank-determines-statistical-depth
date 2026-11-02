module

public import PaperProofs.Paid.PDROC_OverlaySimulator_033
public import PaperProofs.Paid.PDROC_OverlaySuccess_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Native commitments retain their genuine ordinary-write serial. Thus a
stage/tool witness identifies the physically reserialed commitment. -/
theorem overlay_prefix_commitment_of_reservedPair
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Actual : Type*} (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (handle : MismatchHandle I) (tool : I.Tool)
    (hm : (handle.stage, tool) ∈ reservedPairs s.history) :
    (reserialHandle s.history handle, tool) ∈ historyCommitments s.history := by
  obtain ⟨pair, hpair, he⟩ := List.mem_map.mp hm
  have hs : pair.1.stage = handle.stage := congrArg (fun x : I.Stage × I.Tool => x.1) he
  have ht : pair.2 = tool := congrArg (fun x : I.Stage × I.Tool => x.2) he
  have hserial : pair.1.writeSerial = historyWriteSerial s.history pair.1.stage := by
    rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hpair
    obtain ⟨commitment, hc, rfl⟩ := List.mem_map.mp hpair
    exact ((prefix_invariant input C mode accounting rule seed truth tapes hp).commitment_genuine commitment hc).2.trans
      (prefix_historyWriteSerial input C mode accounting rule seed truth tapes hp commitment.handle.stage).symm
  have hh : pair.1 = reserialHandle s.history handle := by
    rcases pair with ⟨⟨other, serial⟩, otherTool⟩
    rcases handle with ⟨target, targetSerial⟩
    dsimp only at hs hserial ⊢
    subst target
    exact congrArg (MismatchHandle.mk other) hserial
  have heq : pair = (reserialHandle s.history handle, tool) := Prod.ext hh ht
  exact heq ▸ hpair

/-- At a wrong actual current stage, source permissions transport to the
real Native guard. Ghost reservations cannot supply physical execution;
the reverse reservation witness is obtained from genuine Native prefixes. -/
theorem overlay_wrong_guard_transport
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    {Actual Source SimSeed : Type*}
    (rule : PolicyRule I Actual) (seed : Actual) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hc : s.cursor = stage.val)
    (hw : s.ledger.written stage = some (!s.ledger.truth stage)) (action : Action I)
    (hallow : historyAllowsAction (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow action) :
    historyAllowsAction s.history (reserialAction s.history (fun _ bit => bit) action) := by
  let ghost := fun _ : SimSeed => overlayGhostAtCache source oldSeed
  let virtual := (overlayReplay draw mark ghost simSeed s.history).shadow
  have hproj := overlayReplay_historyProjection draw mark ghost simSeed s.history
  have hstage (handle : MismatchHandle I) (hcur : historyCursor virtual = handle.stage.val) : handle.stage = stage := by
    apply Fin.ext
    exact hcur.symm.trans (hproj.1.symm.trans ((prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans hc))
  have hvalid (handle : MismatchHandle I) (hcur : historyCursor virtual = handle.stage.val)
      (_hv : historyValidHandle virtual handle) : historyValidHandle s.history (reserialHandle s.history handle) := by
    have hs := hstage handle hcur
    have hv := overlaySuccess_prefix_validHandle_of_wrong input C hearly mode accounting rule seed truth tapes hp stage hw
    simpa only [reserialHandle, hs] using hv
  have hreverse (handle : MismatchHandle I) (tool : I.Tool)
      (hcur : historyCursor virtual = handle.stage.val) (_hv : historyValidHandle virtual handle)
      (hm : (handle, tool) ∈ historyCommitments virtual) :
      (reserialHandle s.history handle, tool) ∈ historyCommitments s.history := by
    have hs := hstage handle hcur
    have hpair : (stage, tool) ∈ reservedPairs virtual := by
      exact hs ▸ (List.mem_map.mpr ⟨(handle, tool), hm, rfl⟩ : (handle.stage, tool) ∈ reservedPairs virtual)
    have ha := overlaySuccess_prefix_wrong_reserve_physical input C hearly mode accounting rule seed truth tapes
      source oldSeed draw mark simSeed hp stage tool hw hpair
    apply overlay_prefix_commitment_of_reservedPair input C mode accounting rule seed truth tapes hp handle tool
    simpa only [hs] using ha
  apply overlay_historyAllowsAction_transport s.history virtual action hproj.1 hproj.2.1 hvalid
    (overlayReplay_used_subset draw mark ghost simSeed s.history)
    (fun pair hp => overlay_commitment_witness_of_pairs (fun _ hm => (overlayReplay_pair_sublists draw mark ghost simSeed s.history).1.subset hm) pair hp)
    (fun pair hp => overlay_execution_witness_of_pairs (fun _ hm => (overlayReplay_pair_sublists draw mark ghost simSeed s.history).2.subset hm) pair hp)
    hreverse hallow

end PDROC
