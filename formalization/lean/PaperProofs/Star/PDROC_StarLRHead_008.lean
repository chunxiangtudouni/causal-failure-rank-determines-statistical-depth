module

public import PaperProofs.Star.PDROC_StarLRHead_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

section Completion

variable (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
  (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
  (accounting : NormalAccounting (starInstance P.tools order))
  (sample : Unit × (P.input order).World)

include P order r C late accounting sample

local notation "R" => run (P.input order) C ResourceMode.uncapped accounting
  (P.starReferenceRule order PortKind.lateRetained r none) sample

theorem reference_run_next_stage (start : ℕ)
    (active : (R start).halted = false)
    (inside : (R start).cursor < (starInstance P.tools order).stageCount)
    (headDone : (R start).cursor = 0 → (R start).ledger.written (firstStage P.tools order) ≠ none) :
    ∃ finish, start ≤ finish ∧ (R finish).halted = false ∧
      (R finish).cursor = (R start).cursor + 1 := by
  let stage : (starInstance P.tools order).Stage := ⟨(R start).cursor, inside⟩
  by_cases openPort : (R start).ledger.written stage = none
  · have nonzero : (R start).cursor ≠ 0 := by
      intro zero
      have ishead : stage = firstStage P.tools order := Fin.ext zero
      exact headDone zero ((congrArg (fun i => (R start).ledger.written i) ishead).symm.trans openPort)
    have data := reference_run_blind_write P order r C late accounting sample start
      active inside nonzero openPort
    have insideNext : (R (start+1)).cursor < (starInstance P.tools order).stageCount := by
      rw [data.2.1]
      exact inside
    have writtenNext : (R (start+1)).ledger.written
        ⟨(R (start+1)).cursor, insideNext⟩ ≠ none := by
      have equal : (⟨(R (start+1)).cursor, insideNext⟩ : (starInstance P.tools order).Stage) = stage :=
        Fin.ext data.2.1
      rw [equal, data.2.2]
      exact Option.some_ne_none _
    have advanced := reference_run_advance_written P order r C late accounting sample (start+1)
      data.1 insideNext writtenNext
    refine ⟨start+1+1, by omega, advanced.1, ?_⟩
    exact advanced.2.trans (congrArg (fun n => n+1) data.2.1)
  · have advanced := reference_run_advance_written P order r C late accounting sample start
      active inside openPort
    exact ⟨start+1, by omega, advanced⟩

theorem reference_finite_head_allWritten (n : ℕ)
    (stop : realPosteriorStop P.channel.experiment r
      ((P.input order).reviewAt sample.2 (firstStage P.tools order)) = n) :
    ∃ finish, allWritten (R finish).ledger := by
  have legal := PStarLR.retained_legal_uncapped P order .lateRetained (by decide) r none C
    late.2.1 late.2.2 accounting (Seed := Unit)
  have headData := reference_run_write_data P order r C accounting sample n stop
  have headActive : (R (n+1)).halted = false := by
    rw [reference_run_write_at_stop P order r C accounting sample n stop]
    rfl
  have headPersist (time : ℕ) (afterHead : n+1 ≤ time) :
      (R time).ledger.written (firstStage P.tools order) ≠ none := by
    obtain ⟨extra, equal⟩ := Nat.exists_eq_add_of_le afterHead
    have written := run_written_some_after (P.input order) C .uncapped accounting
      (P.starReferenceRule order .lateRetained r none) legal sample (n+1) extra
      (firstStage P.tools order) _ headData.1
    rw [← equal] at written
    rw [written]
    exact Option.some_ne_none _
  have reaches : ∀ j ≤ (starInstance P.tools order).stageCount,
      ∃ time, n+1 ≤ time ∧ (R time).halted = false ∧ (R time).cursor = j := by
    intro j
    induction j with
    | zero => intro _; exact ⟨n+1, le_rfl, headActive, headData.2.2⟩
    | succ j ih =>
      intro bound
      obtain ⟨time, afterHead, active, cursor⟩ := ih (by omega)
      have inside : (R time).cursor < (starInstance P.tools order).stageCount := by omega
      obtain ⟨finish, afterTime, nextActive, nextCursor⟩ :=
        reference_run_next_stage P order r C late accounting sample time active inside
          (fun _ => headPersist time afterHead)
      refine ⟨finish, afterHead.trans afterTime, nextActive, ?_⟩
      exact nextCursor.trans (congrArg (fun value => value+1) cursor)
  obtain ⟨finish, _, _, cursor⟩ := reaches (starInstance P.tools order).stageCount le_rfl
  obtain ⟨clock, _, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) legal sample finish
  exact ⟨finish, PStarLR.prefix_allWritten_of_terminal (P.input order) C .uncapped accounting
    (P.starReferenceRule order .lateRetained r none) sample.1 _ _ path cursor⟩

end Completion

theorem original_allWritten_ae (P : PaperProofs.Star.Parameters) (order : Order)
    (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) {r : ℝ}
    (hr : 0 < r) (hrquarter : r ≤ 1/4) :
    ∀ᵐ sample : Unit × (P.input order).World ∂(P.input order).seededWorldLaw (Measure.dirac ()),
      ∃ finish, allWritten (run (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none) sample finish).ledger := by
  filter_upwards [referenceHeadTest_stop_world_ae P order hr (by linarith)] with sample finiteStop
  obtain ⟨n, stop⟩ := ENat.ne_top_iff_exists.mp finiteStop
  exact reference_finite_head_allWritten P order r C late accounting sample n stop.symm

end PDROC.StarLRHead
