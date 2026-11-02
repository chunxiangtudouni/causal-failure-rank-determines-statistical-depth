module

public import PaperProofs.Paid.PDROC_SimulatorFlow_008
public import PaperProofs.Paid.PDROC_TerminalCapture_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {I : Instance} {Seed : Type u}

theorem step_cursor_eq_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} (hs : Step input C mode accounting tapes s action next)
    (hh : next.halted = true) : next.cursor = s.cursor := by
  cases hs <;> first | rfl | cases hh

/-- Halting at the genuine first exit does not advance the cursor. This
prevents a terminal source record from masquerading as active cursor N. -/
theorem halted_minimal_stage_exit_cursor (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (hl : LegalRule input C mode accounting source) (sample : Seed × input.World)
    (start offset : ℕ) (stage : I.Stage)
    (ha : (run input C mode accounting source sample start).halted = false)
    (hbefore : ∀ k < offset, (run input C mode accounting source sample (start + k)).halted = false ∧
      (run input C mode accounting source sample (start + k)).cursor = stage.val)
    (hh : (run input C mode accounting source sample (start + offset)).halted = true) :
    (run input C mode accounting source sample (start + offset)).cursor = stage.val := by
  have hpos : 0 < offset := by
    by_contra hn
    have hz : offset = 0 := by omega
    rw [hz, Nat.add_zero, ha] at hh
    cases hh
  have hb := hbefore (offset - 1) (by omega)
  have hs := run_actualStep_of_active input C mode accounting source hl sample (start + (offset - 1)) hb.1
  have hclock : start + (offset - 1) + 1 = start + offset := by omega
  rw [hclock] at hs
  exact (step_cursor_eq_of_halted input C mode accounting _ hs hh).trans hb.2

/-- Final-cursor tail projection. Never-entry, missing exit and halted exit
remain none; an active cursor-N exit receives the source's exact terminal tail. -/
def finalCursorTailProjection (N : ℕ) (source : PolicyRule I Seed)
    (result : (Seed × EntryHistory I) × EntryHistory I) : Seed × EntryHistory I :=
  (result.1.1, if result.1.2.isSome = true then result.2.bind (fun exit =>
    if historyHalted exit = false ∧ historyCursor exit = N
    then cursorCompletedNatHistory N (some (terminalCursorTail source result.1.1 exit)) else none) else none)

theorem measurable_finalCursorTailProjection [MeasurableSpace Seed] (N : ℕ)
    (source : PolicyRule I Seed) (hm : MeasurableRule source) :
    Measurable (finalCursorTailProjection N source) := by
  classical
  apply measurable_from_prod_countable_left
  intro exit
  cases exit with
  | none =>
    have h := measurable_fst.prodMk (measurable_const : Measurable
      (fun _ : Seed × EntryHistory I => (none : EntryHistory I)))
    simpa only [finalCursorTailProjection, Option.bind_none, ite_self] using h
  | some history =>
    have ht := (measurable_terminalCursorTail source hm).comp
      (measurable_fst.prodMk (measurable_const : Measurable (fun _ : Seed × EntryHistory I => history)))
    have hv := (measurable_of_countable (fun history : List (VisibleEvent I) =>
      cursorCompletedNatHistory N (some history))).comp ht
    have hg : MeasurableSet {pair : Seed × EntryHistory I | pair.2.isSome = true} :=
      ((measurable_of_countable (fun entry : EntryHistory I => entry.isSome)).comp measurable_snd)
        (measurableSet_singleton true)
    by_cases hc : historyHalted history = false ∧ historyCursor history = N
    · have h : Measurable (fun pair : Seed × EntryHistory I => (pair.1,
          if pair.2.isSome = true then cursorCompletedNatHistory N (some (terminalCursorTail source pair.1 history)) else none)) :=
        measurable_fst.prodMk (hv.ite hg measurable_const)
      simpa only [finalCursorTailProjection, hc, ↓reduceIte, Option.bind_some, and_self] using h
    · have h := (measurable_fst.prodMk (measurable_const : Measurable (fun _ : Seed × EntryHistory I => (none : EntryHistory I))))
      simpa only [finalCursorTailProjection, hc, ↓reduceIte, Option.bind_some, ite_self] using h

theorem finalCursorTailProjection_no_prior (N : ℕ) (source : PolicyRule I Seed)
    (seed : Seed) (exit : EntryHistory I) :
    finalCursorTailProjection N source ((seed, none), exit) = (seed, none) := by
  simp only [finalCursorTailProjection, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

theorem finalCursorTailProjection_halted (N : ℕ) (source : PolicyRule I Seed)
    (seed : Seed) (prior : EntryHistory I) (exit : List (VisibleEvent I)) (hh : historyHalted exit = true) :
    finalCursorTailProjection N source ((seed, prior), some exit) = (seed, none) := by
  simp only [finalCursorTailProjection, Option.bind_some, hh, Bool.true_eq_false, false_and, ↓reduceIte, ite_self]

theorem finalCursorTailProjection_active_N (N : ℕ) (source : PolicyRule I Seed)
    (seed : Seed) (prior exit : List (VisibleEvent I)) (hh : historyHalted exit = false)
    (hc : historyCursor exit = N) :
    finalCursorTailProjection N source ((seed, some prior), some exit) =
      (seed, cursorCompletedNatHistory N (some (terminalCursorTail source seed exit))) := by
  simp only [finalCursorTailProjection, Option.isSome_some, Option.bind_some, hh, hc, and_self, ↓reduceIte]

end PDROC




