module

public import PaperProofs.Paid.PDROC_OverlaySuccess_007
public import PaperProofs.Paid.PDROC_SimulatorLaw_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- Before an actual write, even the enlarged virtual ledger has no
current-stage reservation. Extra virtual reservations require a genuine
actually correct write; physical reservations require a genuine write. -/
theorem overlay_prefix_shadow_no_commitment_of_unwritten
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    {Actual Source SimSeed : Type*} (rule : PolicyRule I Actual) (seed : Actual)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (source : PolicyRule I Source) (oldSeed : Source)
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (mark : SimSeed → I.Stage → AuxiliaryRecord → Bool) (simSeed : SimSeed)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (stage : I.Stage) (hw : s.ledger.written stage = none) :
    ∀ pair ∈ historyCommitments
        (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow,
      pair.1.stage ≠ stage := by
  intro pair hm hs
  have hv : (pair.1.stage, pair.2) ∈ reservedPairs
      (overlayReplay draw mark (fun _ => overlayGhostAtCache source oldSeed) simSeed s.history).shadow :=
    List.mem_map.mpr ⟨pair, hm, rfl⟩
  rcases overlaySuccess_prefix_reserve_covered input C hearly mode accounting rule seed truth tapes
      source oldSeed draw mark simSeed hp _ hv with hc | hr
  · rw [hs, hw] at hc
    cases hc
  · obtain ⟨physical, hphysical, heq⟩ := List.mem_map.mp hr
    rw [prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hphysical
    obtain ⟨commitment, hcommit, hpair⟩ := List.mem_map.mp hphysical
    have hphysicalStage : physical.1.stage = stage := (congrArg Prod.fst heq).trans hs
    have hstage : commitment.handle.stage = stage :=
      (congrArg (fun pair : MismatchHandle I × I.Tool => pair.1.stage) hpair).trans hphysicalStage
    have hg := ((prefix_invariant input C mode accounting rule seed truth tapes hp).commitment_genuine commitment hcommit).1
    rw [hstage, hw] at hg
    cases hg

universe u
variable {Seed : Type u}

theorem overlay_entry_shadow_no_current_commitment
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry) :
    ∀ pair ∈ historyCommitments (overlayShadow P source sample.1 entry), pair.1.stage ≠ stage := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨start, hc, hb, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  have hfirst : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hb⟩
  have hu := (firstEntryAt_unborn input C.val .uncapped accounting actual hl sample stage.val start hfirst).2
  obtain ⟨an, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have h := overlay_prefix_shadow_no_commitment_of_unwritten input C.val C.property.1.1 .uncapped accounting
    actual sample.1 (input.truthAt sample.2) (worldTapes input sample.2) source sample.1.1
    (overlaySeedDraw P source) (overlaySeedMark P) sample.1 hp stage (hu stage le_rfl).1
  rw [hh] at h
  exact h

theorem historyCommitments_sourceDrawTerminalHistory (stage : I.Stage) (entry : List (VisibleEvent I))
    (draw : SimulatorDraw I) (truth : Bool) :
    historyCommitments (sourceDrawTerminalHistory stage entry draw truth) = historyCommitments entry := by
  cases ha : draw.action <;>
    simp [sourceDrawTerminalHistory, ha, historyCommitments, simulatorReviewPacket, eventCommitment, Function.comp_def]

theorem overlay_entry_sourcePacket_no_current_commitment
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (overlayRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance) (truth : Bool) :
    ∀ pair ∈ historyCommitments
        (sourceDrawTerminalHistory stage (overlayShadow P source sample.1 entry) draw truth),
      pair.1.stage ≠ stage := by
  rw [historyCommitments_sourceDrawTerminalHistory]
  exact overlay_entry_shadow_no_current_commitment P fee hfee C accounting source sample stage entry he

end PDROC
