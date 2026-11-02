module

public import PaperProofs.Star.PStarLR_LateHaltWritten_020
public import PaperProofs.Star.PStarLR_TerminalCriterion_019

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

variable {I : Instance}

theorem run_halts_of_tail_review_bound (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (legal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (start : ℕ) (quota : I.Stage → ℕ)
    (bounded : ∀ extra stage, (run input C mode accounting rule sample (start+extra)).ledger.reviews stage ≤ quota stage) :
    ∃ n, start ≤ n ∧ (run input C mode accounting rule sample n).halted = true := by
  classical
  let bound := reviewBoundedActionBound I quota
  by_contra never
  have active : (run input C mode accounting rule sample (start+bound+1)).halted = false := by
    apply Bool.eq_false_iff.mpr
    intro halted
    exact never ⟨start+bound+1, by omega, halted⟩
  have path := run_prefix_of_active input C mode accounting rule legal sample (start+bound+1) active
  have bounds : ∀ stage, (run input C mode accounting rule sample (start+bound+1)).ledger.reviews stage ≤ quota stage := by
    intro stage
    simpa only [Nat.add_assoc] using bounded (bound+1) stage
  have length := prefix_length_le_of_reviews_bounded input C mode accounting rule sample.1
    (input.truthAt sample.2) (worldTapes input sample.2) path quota bounds
  change start+bound+1 ≤ bound at length
  omega

theorem late_run_finishes_after_head_write (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World)
    (start : ℕ) (bit : Bool)
    (written : (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
      sample start).ledger.written (firstStage P.tools order) = some bit) :
    ∃ n, start ≤ n ∧
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n).halted = true ∧
      allWritten (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none) sample n).ledger := by
  classical
  have legal := retained_legal_uncapped P order .lateRetained (by decide) r none C late.2.1 late.2.2 accounting
    (Seed := Unit)
  have finite := (run_finiteCounters (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample start).1 (firstStage P.tools order)
  obtain ⟨count, hcount⟩ : ∃ count : ℕ,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
        sample start).ledger.reviews (firstStage P.tools order) = count := by
    lift (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
      sample start).ledger.reviews (firstStage P.tools order) to ℕ using finite with count
    exact ⟨count, rfl⟩
  let quota : (starInstance P.tools order).Stage → ℕ := fun stage =>
    if stage = firstStage P.tools order then count else 0
  have bounded : ∀ extra stage,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
        sample (start+extra)).ledger.reviews stage ≤ quota stage := by
    intro extra stage
    by_cases head : stage = firstStage P.tools order
    · subst stage
      rw [run_reviews_written_port (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) legal sample start extra _ bit written, hcount]
      simp [quota]
    · have nonzero : stage.val ≠ 0 := by
        intro zero
        apply head
        apply Fin.ext
        exact zero
      rw [late_run_other_reviews_zero_of_legal P order r none C .uncapped accounting legal sample
        (start+extra) stage nonzero]
      simp [quota, head]
  obtain ⟨n, later, halted⟩ := run_halts_of_tail_review_bound (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample start quota bounded
  obtain ⟨_clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample n
  have complete := late_halted_prefix_allWritten P order r C .uncapped accounting sample.1
    ((P.input order).truthAt sample.2) (worldTapes (P.input order) sample.2) path halted
  exact ⟨n, later, halted, complete⟩

theorem late_terminalCriterion_of_ae_head_write (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order))
    (headWritten : ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())), ∃ start bit,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none)
        sample start).ledger.written (firstStage P.tools order) = some bit) :
    P.TerminalCriterion order .lateRetained r C accounting := by
  apply retained_terminalCriterion_of_ae_allWritten P order .lateRetained (by decide) r C late.2.1 late.2.2 accounting
  filter_upwards [headWritten] with sample written
  obtain ⟨start, bit, written⟩ := written
  obtain ⟨n, _later, _halted, complete⟩ := late_run_finishes_after_head_write P order r C late accounting
    sample start bit written
  exact ⟨n, complete⟩

end PStarLR
