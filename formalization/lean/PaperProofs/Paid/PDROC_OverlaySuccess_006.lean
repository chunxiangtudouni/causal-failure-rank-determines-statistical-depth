module

public import PaperProofs.Paid.PDROC_OverlaySuccess_005
public import PaperProofs.Paid.PDROC_OverlaySimulator_031

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Original D14 deterministic prefix-success domination for the concrete
record-aware overlay. Every sample and every finite prefix are covered. -/
theorem overlay_prefix_success_domination (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) :
    ∀ (sample : OverlaySeed P Seed × (P.input fee hfee).World) (n : ℕ),
      let virtual := (overlayData P source).shadow sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting (overlayRule P fee hfee source) sample := by
  intro sample n
  dsimp only
  intro hs
  have hl := overlayRule_legal P fee hfee C accounting source
  obtain ⟨k, _, hp⟩ := run_has_prefix (P.input fee hfee) C.val .uncapped accounting
    (overlayRule P fee hfee source) hl sample n
  have herror := overlay_actual_error_prefix P fee hfee C accounting source sample n
  have hsuccess := overlaySuccess_prefix_success_of_error (P.input fee hfee) C.val C.property.1.1
    .uncapped accounting (overlayRule P fee hfee source) sample.1 _ _ source sample.1.1
    (overlaySeedDraw P source) (overlaySeedMark P) sample.1 hp herror hs.1 hs.2
  exact ⟨n, hsuccess.1, hsuccess.2⟩

/-- The same original field with the publicly packaged overlay policy. -/
theorem overlayPolicy_prefix_success_domination (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed) :
    ∀ (sample : OverlaySeed P Seed × (P.input fee hfee).World) (n : ℕ),
      let virtual := (overlayData P source.rule).shadow sample.1
        (run (P.input fee hfee) C.val .uncapped accounting
          (overlayPolicy P fee hfee C accounting source).rule sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting
          (overlayPolicy P fee hfee C accounting source).rule sample :=
  overlay_prefix_success_domination P fee hfee C accounting source.rule

end PDROC
