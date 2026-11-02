module

public import PaperProofs.Star.PDROC_StarFirstExit_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarFirstExit.Local

theorem realStop_le_iff (E : PaperProofs.Statistics.BinaryExperiment) (target : ℝ)
    (tape : E.Tape) (n : ℕ) : realPosteriorStop E target tape ≤ n ↔
      ∃ k ≤ n, Real.log ((1-target)/target) ≤ |E.logOddsScore tape k| := by
  classical
  let hits : Set ℕ∞ := {t | ∃ k : ℕ, t = k ∧ Real.log ((1-target)/target) ≤ |E.logOddsScore tape k|}
  change sInf hits ≤ (n : ℕ∞) ↔ _
  constructor
  · intro hs
    have nonempty : hits.Nonempty := by
      by_contra absent
      rw [Set.not_nonempty_iff_eq_empty.mp absent, sInf_empty] at hs
      exact ENat.top_ne_natCast n (top_le_iff.mp hs).symm
    obtain ⟨k, hk, hit⟩ := csInf_mem nonempty
    refine ⟨k, ?_, hit⟩
    rw [hk] at hs
    exact ENat.natCast_le_natCast.mp hs
  · rintro ⟨k, hkn, hit⟩
    exact (sInf_le (show (k : ℕ∞) ∈ hits from ⟨k, rfl, hit⟩)).trans (by exact_mod_cast hkn)

theorem realStop_before (E : PaperProofs.Statistics.BinaryExperiment) (target : ℝ)
    (tape : E.Tape) (n : ℕ) (before : (n : ℕ∞) < realPosteriorStop E target tape) :
    |E.logOddsScore tape n| < Real.log ((1-target)/target) := by
  apply lt_of_not_ge
  intro hit
  exact (not_le_of_gt before) ((realStop_le_iff E target tape n).mpr ⟨n, le_rfl, hit⟩)

theorem realStop_hits (E : PaperProofs.Statistics.BinaryExperiment) (target : ℝ)
    (tape : E.Tape) (n : ℕ) (stop : realPosteriorStop E target tape = n) :
    Real.log ((1-target)/target) ≤ |E.logOddsScore tape n| := by
  obtain ⟨k, hkn, hit⟩ := (realStop_le_iff E target tape n).mp (by rw [stop])
  have hnk : n ≤ k := by
    have hle := (realStop_le_iff E target tape k).mpr ⟨k, le_rfl, hit⟩
    rw [stop] at hle
    exact ENat.natCast_le_natCast.mp hle
  simpa only [Nat.le_antisymm hkn hnk] using hit

/-- This is an actual entry state in the existing global interpreter. -/
structure Entry (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage) : Prop where
  live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock) i
  unwritten : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock).ledger.written i = none
  reviews_zero : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample entryClock).ledger.reviews i = 0

/-- A local conditional interface. Actual outer-selector stability is proved
separately by the retained assembly; it was not a premise of original FirstExit. -/
def StableTarget (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (entryClock : ℕ) (i : (starInstance P.tools order).Stage)
    (target : ℝ) : Prop :=
  ∀ offset : ℕ,
    let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample (entryClock+offset)
    liveStage s i → s.ledger.written i = none → P.chosenTargetReal order kind r s.history i = some target

theorem actual_action (P : PaperProofs.Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (sample : Unit × (P.input order).World) (clock : ℕ) (i : (starInstance P.tools order).Stage)
    (live : liveStage (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock) i)
    (port : (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.written i = none) :
    P.starReferenceRule order kind r none sample.1
      (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history =
      match P.chosenTargetReal order kind r
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).history i with
      | none => .write i false
      | some target =>
        if Real.log ((1-target)/target) ≤ |P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i)
          ((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.reviews i).toNat| then
          .write i (decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i)
            ((run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample clock).ledger.reviews i).toNat))
        else .review i := by
  rcases sample with ⟨⟨⟩, world⟩
  have hp := run_prefix_of_active_no_legal (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r none (Seed := Unit)) ((),world) clock live.1
  exact (rule_testing_of_live_unwritten P order kind r C accounting ((P.input order).truthAt world)
    (worldTapes (P.input order) world) hp i live port).trans
      (testingAction_actual P order kind r C accounting ((P.input order).truthAt world)
        (worldTapes (P.input order) world) hp i)

end PDROC.StarFirstExit.Local
