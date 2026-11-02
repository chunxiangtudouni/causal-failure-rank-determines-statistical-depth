module

public import PaperProofs.Paid.PDROC_Termination_001
public import PaperProofs.Paid.PDROC_StageObservables_002
public import PaperProofs.Common.ReferenceGlobalCost
public import Mathlib.Data.ENat.BigOperators

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

theorem paidRunReviewCount_of_no_entry (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World) (stage : P.sharedInstance.Stage)
    (hnone : entryHistory (P.input fee hfee) C.val mode accounting rule stage sample = none) :
    P.paidRunReviewCount fee hfee C mode accounting rule sample stage = 0 := by
  have hz (clock : ℕ) : (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.reviews stage = 0 :=
    (run_cursorInvariant (P.input fee hfee) C.val mode accounting rule hl sample clock).future_reviews stage
      (run_cursor_lt_of_no_entry (P.input fee hfee) C.val mode accounting rule hl sample stage hnone clock)
  simp only [PaperProofs.Paid.Parameters.paidRunReviewCount, hz, iSup_const]

theorem paid_finiteReviewCounts_exists_halt (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) {Seed : Type*} [MeasurableSpace Seed]
    (rule : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val mode accounting rule)
    (sample : Seed × (P.input fee hfee).World)
    (hc : ∀ stage, P.paidRunReviewCount fee hfee C mode accounting rule sample stage ≠ ⊤) :
    ∃ clock, (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = true := by
  have hsum : (∑ stage, P.paidRunReviewCount fee hfee C mode accounting rule sample stage) ≠ ⊤ :=
    ENat.sum_ne_top.mpr (fun stage _ => hc stage)
  obtain ⟨Q, hQ⟩ := ENat.ne_top_iff_exists.mp hsum
  have hbound (clock : ℕ) : (∑ stage, (run (P.input fee hfee) C.val mode accounting rule sample clock).ledger.reviews stage) ≤
      (Q : ℕ∞) := by
    rw [hQ]
    exact Finset.sum_le_sum (fun stage _ => le_iSup
      (fun k => (run (P.input fee hfee) C.val mode accounting rule sample k).ledger.reviews stage) clock)
  by_contra hn
  let clock := Q + P.sharedInstance.toolCount + P.sharedInstance.toolCount +
    P.sharedInstance.stageCount + P.sharedInstance.stageCount + 1 + 1
  have ha : (run (P.input fee hfee) C.val mode accounting rule sample clock).halted = false :=
    Bool.eq_false_iff.mpr (fun hh => hn ⟨clock, hh⟩)
  have hp := run_prefix_of_active (P.input fee hfee) C.val mode accounting rule hl sample clock ha
  have hle := prefix_progress_le_of_review_sum (P.input fee hfee) C.val mode accounting rule sample.1
    ((P.input fee hfee).truthAt sample.2) (worldTapes (P.input fee hfee) sample.2) hp Q (hbound clock)
  rw [prefix_actionProgress (P.input fee hfee) C.val mode accounting rule sample.1 _ _ hp] at hle
  have hh := ENat.natCast_le_natCast.mp hle
  dsimp only [clock] at hh
  omega

/-- The original boundary stage-realization conclusion already forces actual
termination. It never requires finite expected fees or SourceHistoryLaw. -/
theorem boundaryStageRealization_completedHistory_none_zero (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) {SourceSeed SimSeed : Type*}
    [MeasurableSpace SimSeed] (ν : Measure SimSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (hr : P.BoundaryStageRealization fee hfee C accounting ν actual.rule data) :
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
          obtain ⟨n, _hstop, hcount, _hdecision⟩ := h
          rw [hcount]
          exact ENat.natCast_ne_top n
    intro hn
    exact ((completedHistory_none_iff (P.input fee hfee) C.val .uncapped accounting actual.rule sample).mp hn)
      (paid_finiteReviewCounts_exists_halt P fee hfee C .uncapped accounting actual.rule actual.legal sample hc)
  simpa only [not_not] using ae_iff.mp hae

end PDROC
