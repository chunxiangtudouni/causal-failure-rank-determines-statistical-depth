module

public import PaperProofs.Paid.PDROC_OverlaySimulator_020
public import PaperProofs.Paid.PDROC_Termination_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Stage implementation alone forces actual return. In particular this
proof is independent of SourceHistoryLaw and expected-cost finiteness. -/
theorem overlayStageRealization_completedHistory_none_zero (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {SourceSeed SimSeed : Type*}
    [MeasurableSpace SimSeed] (ν : Measure SimSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlayDraft.OverlaySimulatorData P.sharedInstance SourceSeed SimSeed)
    (hr : OverlayDraft.OverlayStageRealization P fee hfee C accounting ν actual.rule data) :
    (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0 := by
  have hae : ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
      completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample ≠ none := by
    filter_upwards [hr] with sample hs
    have hc : ∀ stage, P.paidRunReviewCount fee hfee C .uncapped accounting actual.rule sample stage ≠ ⊤ := by
      intro stage
      cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting actual.rule stage sample with
      | none => rw [paidRunReviewCount_of_no_entry P fee hfee C .uncapped accounting actual.rule actual.legal sample stage he]; simp
      | some entry =>
        have h := hs stage entry he
        dsimp only at h
        cases hd : (data.record sample.1 stage entry).decision with
        | none =>
          rw [hd] at h
          rw [h.2]
          simp
        | some decision =>
          rw [hd] at h
          obtain ⟨n, _hstop, hcount, _hdecision, _hmap⟩ := h
          rw [hcount]
          exact ENat.natCast_ne_top n
    intro hn
    exact ((completedHistory_none_iff (P.input fee hfee) C.val .uncapped accounting actual.rule sample).mp hn)
      (paid_finiteReviewCounts_exists_halt P fee hfee C .uncapped accounting actual.rule actual.legal sample hc)
  simpa only [not_not] using ae_iff.mp hae


/-- The concrete actual paid overlay returns almost surely. The source
policy may use an arbitrary private-seed universe; no source-history law,
finite-ET or expected paid-bill assumption is needed. -/
theorem overlay_completedHistory_none_zero (P : Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed)
    (ν : Measure (OverlaySeed P Seed)) [IsProbabilityMeasure ν] :
    (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting
        (overlayPolicy P fee hfee C accounting source).rule sample = none} = 0 :=
  overlayStageRealization_completedHistory_none_zero P fee hfee C accounting ν
    (overlayPolicy P fee hfee C accounting source) (overlayData P source.rule)
    (overlayStageRealization P fee hfee C accounting source.rule ν)

end PDROC
