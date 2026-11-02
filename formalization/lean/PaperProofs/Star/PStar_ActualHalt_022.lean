module

public import PaperProofs.Star.PStar_StopLaw_018
public import PaperProofs.Star.PStar_CurrentLegality_006
public import PaperProofs.Star.PStarLR_PostHeadCompletion_021
public import PaperProofs.Star.PDROC_StarFirstExit_Local_004
public import PaperProofs.Star.RootStarQuota_002
public import Mathlib.Order.SuccPred.ENat

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarActualHalt022

open Common Common.Native Parameters MeasureTheory PStarLR PStarCurrentLegality006 PStarStopLaw018

theorem reference_legal (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r none (Seed := Unit)) := by
  cases kind with
  | current => exact current_legal_uncapped P order r none C accounting
  | earlyRetained => exact retained_legal_uncapped P order .earlyRetained (by decide) r none C qualified.2.1 qualified.2.2 accounting
  | lateRetained => exact retained_legal_uncapped P order .lateRetained (by decide) r none C qualified.2.1 qualified.2.2 accounting

/-- Every actual count is bounded by a fixed test on that same stage's tape.
The bound follows from original current-target review semantics and r/5;
no entry identification, stability, success or finite-ET premise is supplied. -/
theorem prefix_reviews_le_floorStop (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (positive : 0 < r) (quarter : r ≤ 1/4)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
      sample.1 ((P.input order).truthAt sample.2) (worldTapes (P.input order) sample.2) n state) :
    ∀ stage : (starInstance P.tools order).Stage, state.ledger.reviews stage ≤
      realPosteriorStop P.channel.experiment (r/5) ((P.input order).reviewAt sample.2 stage) := by
  classical
  induction path with
  | initial => intro stage; exact zero_le
  | @next n state next earlier step ih =>
    generalize selected : P.starReferenceRule order kind r none sample.1 state.history = action at step
    cases step with
    | review stage live port resources =>
      intro other
      by_cases same : other = stage
      · subst other
        simp only [record, reviewLedger, Function.update_self]
        have sourceEq : run (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) sample n = state := by
          have reconstructed : replayWorld (P.input order) ((P.input order).truthAt sample.2)
              (worldTapes (P.input order) sample.2) = sample.2 := rfl
          simpa only [reconstructed] using prefix_eq_run (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind r none) sample.1 ((P.input order).truthAt sample.2)
            (worldTapes (P.input order) sample.2) earlier
        obtain ⟨target, chosen, before⟩ := PDROC.StarFirstExit.Local.review_current_before_stop
          P order kind r C accounting sample n stage
          (by rw [sourceEq]; exact live) (by rw [sourceEq]; exact port)
          (by rw [sourceEq]; exact selected)
        have bounds := RootStarQuota.chosenTarget_bounds P order kind r positive quarter _ stage target chosen
        have stopBound := realPosteriorStop_antitone P.channel.experiment (r/5) target
          (by positivity) bounds.1 bounds.2 ((P.input order).reviewAt sample.2 stage)
        have beforeFloor := before.trans_le stopBound
        rw [sourceEq] at beforeFloor
        exact (ENat.add_one_le_iff (prefix_reviews_finite (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none) sample.1 _ _ earlier stage)).mpr beforeFloor
      · change Function.update state.ledger.reviews stage (state.ledger.reviews stage + 1) other ≤ _
        rw [Function.update_of_ne same]
        exact ih other
    | write =>
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | allocate | execute | advance | stop | abandon => exact ih

theorem run_reviews_le_floorStop (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (positive : 0 < r) (quarter : r ≤ 1/4)
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) (sample : Unit × (P.input order).World)
    (n : ℕ) (stage : (starInstance P.tools order).Stage) :
    (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).ledger.reviews stage ≤
      realPosteriorStop P.channel.experiment (r/5) ((P.input order).reviewAt sample.2 stage) := by
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) (reference_legal P order kind r C qualified accounting) sample n
  exact prefix_reviews_le_floorStop P order kind r positive quarter C accounting sample path stage

/-- Genuine ideal-run termination is derived from fixed local finite stops.
It is an a.e. conclusion, never an extra condition on a comparator or H0. -/
theorem original_halts_ae (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (positive : 0 < r) (quarter : r ≤ 1/4)
    (C : Contract (starInstance P.tools order)) (qualified : kind.contracts C)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    ∀ᵐ sample : Unit × (P.input order).World ∂(P.input order).seededWorldLaw (Measure.dirac ()),
      ∃ n, (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n).halted = true := by
  filter_upwards [all_realPosteriorStops_world_ae P order (r/5) (by positivity) (by linarith)] with sample finite
  let quota : (starInstance P.tools order).Stage → ℕ := fun stage =>
    (realPosteriorStop P.channel.experiment (r/5) ((P.input order).reviewAt sample.2 stage)).toNat
  have bounded : ∀ extra stage,
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none)
        sample (0+extra)).ledger.reviews stage ≤ quota stage := by
    intro extra stage
    have bound := run_reviews_le_floorStop P order kind r positive quarter C qualified accounting sample extra stage
    have cast : (quota stage : ℕ∞) =
        realPosteriorStop P.channel.experiment (r/5) ((P.input order).reviewAt sample.2 stage) :=
      ENat.natCast_toNat (finite stage)
    change _ ≤ (quota stage : ℕ∞)
    rw [cast]
    simpa only [Nat.zero_add] using bound
  obtain ⟨n, _after, halted⟩ := run_halts_of_tail_review_bound (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none) (reference_legal P order kind r C qualified accounting) sample 0 quota bounded
  exact ⟨n, halted⟩

end PaperProofs.Star.PStarActualHalt022
