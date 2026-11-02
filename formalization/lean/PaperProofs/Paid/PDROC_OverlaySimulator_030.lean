module

public import PaperProofs.Paid.PDROC_OverlaySimulator_029

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem overlay_actualError_of_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (bit : Bool)
    (hd : P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) sample stage = some bit) :
    P.actualWriteError fee hfee C accounting (overlayRule P fee hfee source) stage sample ↔
      (bit != (P.input fee hfee).truthAt sample.2 stage) = true := by
  unfold PaperProofs.Paid.Parameters.actualWriteError
  rw [hd]
  cases bit <;> cases ht : (P.input fee hfee).truthAt sample.2 stage <;> simp

omit [MeasurableSpace Seed] in
theorem overlay_actualFlag_of_some (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : OverlaySeed P Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) (bit : Bool)
    (hd : P.actualOrdinaryDecision fee hfee C .uncapped accounting (overlayRule P fee hfee source) sample stage = some bit) :
    P.actualWriteErrorFlag fee hfee C accounting (overlayRule P fee hfee source) stage sample =
      (bit != (P.input fee hfee).truthAt sample.2 stage) := by
  unfold PaperProofs.Paid.Parameters.actualWriteErrorFlag
  rw [hd]
  cases bit <;> cases ht : (P.input fee hfee).truthAt sample.2 stage <;> rfl

/-- Complete original record-aware D14 all-PATH target for the concrete
Native overlay. There is no source-law, measure-one, successful-path,
finite-time, expected-cost, MAP-source or pureGood premise. -/
theorem overlayPathCoupling (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) :
    OverlayDraft.OverlayPathCoupling P fee hfee C accounting (overlayRule P fee hfee source) (overlayData P source) := by
  let input := P.input fee hfee
  let actual := overlayRule P fee hfee source
  have hl := overlayRule_legal P fee hfee C accounting source
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sample n
    exact overlayData_physical_subsequences P fee hfee C accounting source sample n
  · intro sample stage herror
    have hd : P.actualOrdinaryDecision fee hfee C .uncapped accounting actual sample stage = some (!input.truthAt sample.2 stage) := herror
    obtain ⟨entry, clock, decision, _he, _hd, _hw, hpkt, _ht⟩ :=
      overlay_ordinary_packet_witness P fee hfee C accounting source sample stage (!input.truthAt sample.2 stage) hd
    refine ⟨clock, ?_⟩
    change reportedWriteError (overlayShadow P source sample.1 (run input C.val .uncapped accounting actual sample clock).history) stage = some true
    rw [hpkt]
    cases ht : input.truthAt sample.2 stage <;> rfl
  · intro sample stage entry decision he _hd hreport
    obtain ⟨reportClock, hreport⟩ := hreport
    obtain ⟨bit, hbit⟩ := overlay_actual_report_written P fee hfee C accounting source sample reportClock stage hreport
    have hd := actualOrdinaryDecision_of_written P fee hfee C .uncapped accounting actual hl sample reportClock stage bit hbit
    obtain ⟨entry', clock, decision', he', _hd', hw, hpkt, _ht⟩ :=
      overlay_ordinary_packet_witness P fee hfee C accounting source sample stage bit hd
    have heq : entry' = entry := Option.some.inj (he'.symm.trans he)
    subst entry'
    rw [overlay_virtual_error_at_written P fee hfee C accounting source sample stage clock bit hw, hpkt]
    change some ((bit != input.truthAt sample.2 stage) || overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry)) = some true ↔
      P.actualWriteError fee hfee C accounting actual stage sample ∨
        overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry) = true
    rw [overlay_actualError_of_some P fee hfee C accounting source sample stage bit hd]
    cases hb : (bit != input.truthAt sample.2 stage) <;>
      cases hm : overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry) <;> decide
  · intro sample n stage
    dsimp only
    intro hvirtual
    have hreal := (overlayData_report_not_early P source sample.1 (run input C.val .uncapped accounting actual sample n).history stage).mp hvirtual
    refine ⟨hreal, ?_⟩
    intro entry decision he hdecision
    obtain ⟨bit, hbit⟩ := overlay_actual_report_written P fee hfee C accounting source sample n stage hreal
    have hd := actualOrdinaryDecision_of_written P fee hfee C .uncapped accounting actual hl sample n stage bit hbit
    obtain ⟨entry', clock, decision', he', hd', hw, _hpkt, htruth⟩ :=
      overlay_ordinary_packet_witness P fee hfee C accounting source sample stage bit hd
    have heq : entry' = entry := Option.some.inj (he'.symm.trans he)
    subst entry'
    have hdeq : decision' = decision := Option.some.inj (hd'.symm.trans hdecision)
    subst decision'
    have hframe := (overlay_written_shadow_frames P fee hfee C accounting source sample stage clock n bit bit hw hbit).2
    change (historyReport (overlayShadow P source sample.1 (run input C.val .uncapped accounting actual sample n).history) stage).map Prod.fst =
      some (Bool.xor decision (P.actualWriteErrorFlag fee hfee C accounting actual stage sample ||
        overlaySeedMark P sample.1 stage ((overlayData P source).record sample.1 stage entry)))
    rw [hframe, htruth, overlay_actualFlag_of_some P fee hfee C accounting source sample stage bit hd]
    rfl
  · intro sample n
    exact overlayPolicy_execution_count P fee hfee C accounting source sample n

end PDROC
