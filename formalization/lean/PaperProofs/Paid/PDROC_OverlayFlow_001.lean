module

public import PaperProofs.Paid.PDROC_OverlayLaw_007
public import PaperProofs.Paid.PDROC_SimulatorFlow_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- A genuine minimal exit of the actual controller determines the next
full virtual entry. Both missing prior entry and early halt remain none. -/
theorem overlayVirtualEntryGate_next_of_minimal_exit (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage next : P.sharedInstance.Stage)
    (hnext : next.val = stage.val + 1)
    (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (hcapture : OverlayMinimalExitCaptured P fee hfee C accounting source stage sample) :
    overlayVirtualEntryGate P fee hfee C accounting source next sample =
      simulatorNextEntryOptionalProjection next
        (overlayEventualStageExit P fee hfee C accounting source stage sample) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  let view := overlayShadow P source sample.1
  have hl := overlayRule_legal P fee hfee C accounting source
  cases he : entryHistory input C.val .uncapped accounting actual stage sample with
  | none =>
    have hn := entryHistory_next_none_of_prior_none input C.val .uncapped accounting actual
      hl sample stage next (by omega) he
    have hleft : overlayVirtualEntryGate P fee hfee C accounting source next sample =
        (sample.1.1, none) := by
      change (sample.1.1, (entryHistory input C.val .uncapped accounting actual next sample).map view) = _
      rw [hn, Option.map_none]
    have hprior : (overlayEventualStageExit P fee hfee C accounting source stage sample).1 =
        (sample.1.1, none) := by
      rw [overlayEventualStageExit_prior]
      change (sample.1.1, (entryHistory input C.val .uncapped accounting actual stage sample).map view) = _
      rw [he, Option.map_none]
    rw [hleft]
    symm
    change simulatorNextEntryOptionalProjection next
      ((overlayEventualStageExit P fee hfee C accounting source stage sample).1,
        (overlayEventualStageExit P fee hfee C accounting source stage sample).2) = _
    rw [hprior]
    exact simulatorNextEntryOptionalProjection_no_prior next _ _
  | some entry =>
    obtain ⟨start, offset, hfirst, hbefore, hx, hexit⟩ := hcapture entry he
    have hfields :
        historyCursor (view (run input C.val .uncapped accounting actual sample (start + offset)).history) =
          (run input C.val .uncapped accounting actual sample (start + offset)).cursor ∧
        historyHalted (view (run input C.val .uncapped accounting actual sample (start + offset)).history) =
          (run input C.val .uncapped accounting actual sample (start + offset)).halted := by
      obtain ⟨n, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample (start + offset)
      have hprojection := overlayReplay_historyProjection (overlaySeedDraw P source)
        (overlaySeedMark P) (overlaySeedGhost P source) sample.1
        (run input C.val .uncapped accounting actual sample (start + offset)).history
      exact ⟨hprojection.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ hp),
        hprojection.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual sample.1 _ _ hp)⟩
    have hflow := entryHistory_map_projection_of_minimal_stage_exit input C.val .uncapped accounting
      actual hl sample start offset stage next hnext hfirst.1
      (fun k hk => (hbefore k hk).2) hexit view hfields.2 hfields.1 sample.1.1 (view entry)
    have hprior : (overlayEventualStageExit P fee hfee C accounting source stage sample).1 =
        (sample.1.1, some (view entry)) := by
      rw [overlayEventualStageExit_prior]
      change (sample.1.1, (entryHistory input C.val .uncapped accounting actual stage sample).map view) = _
      rw [he, Option.map_some]
    have hresult : overlayEventualStageExit P fee hfee C accounting source stage sample =
        ((sample.1.1, some (view entry)),
          some (view (run input C.val .uncapped accounting actual sample (start + offset)).history)) :=
      Prod.ext hprior hx
    rw [hresult, simulatorNextEntryOptionalProjection_some]
    exact hflow

/-- Almost-everywhere actual capture feeds the next-entry law composition
without any added entry-law or source-history-law assumption. -/
theorem overlayVirtualEntryGate_next_ae_of_minimal_exit [MeasurableSpace Seed]
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (OverlaySeed P Seed))
    (stage next : P.sharedInstance.Stage) (hnext : next.val = stage.val + 1)
    (hcapture : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      OverlayMinimalExitCaptured P fee hfee C accounting source stage sample) :
    ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      overlayVirtualEntryGate P fee hfee C accounting source next sample =
        simulatorNextEntryOptionalProjection next
          (overlayEventualStageExit P fee hfee C accounting source stage sample) :=
  hcapture.mono (fun sample hc =>
    overlayVirtualEntryGate_next_of_minimal_exit P fee hfee C accounting source stage next hnext sample hc)

end PDROC
