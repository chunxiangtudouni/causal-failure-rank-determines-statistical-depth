module

public import PaperProofs.Paid.PDROC_SimulatorLaw_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance} {Seed : Type*}

theorem completedHistory_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (source : PolicyRule I Seed)
    (sample : Seed × input.World) (start : ℕ)
    (hh : (run input C mode accounting source sample start).halted = true) :
    completedHistory input C mode accounting source sample =
      some (run input C mode accounting source sample start).history := by
  classical
  have hex : ∃ n, (run input C mode accounting source sample n).halted = true := ⟨start, hh⟩
  have hle : Nat.find hex ≤ start := Nat.find_min' hex hh
  have hr := run_after_halt input C mode accounting source sample (Nat.find hex)
    (Nat.find_spec hex) (start - Nat.find hex)
  rw [Nat.add_sub_of_le hle] at hr
  simp only [completedHistory, dite_eq_left hex]
  exact congrArg some (congrArg (fun state : State I => state.history) hr.symm)

/-- At terminal cursor N, a genuine current-payment source can only stop
or abandon, including the zero-stage instance. -/
theorem currentPayment_terminalCursor_action_cases (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ)
    (ha : (run input C mode accounting source sample start).halted = false)
    (hc : (run input C mode accounting source sample start).cursor = I.stageCount) :
    source sample.1 (run input C mode accounting source sample start).history = .stop ∨
      source sample.1 (run input C mode accounting source sample start).history = .abandon := by
  obtain ⟨n, _, hp⟩ := run_has_prefix input C mode accounting source hl sample start
  obtain ⟨next, hs⟩ := hl sample.1 _ _ n _ hp ha
  generalize haction : source sample.1 (run input C mode accounting source sample start).history = action at hs ⊢
  cases hs with
  | review stage live port resources | write stage bit live port resources | advance stage live written resources =>
    have hi := stage.isLt
    change stage.val < I.stageCount at hi
    have hlive := live.2
    omega
  | allocate handle tool active valid compatible unused unallocated window resources =>
    have hw := window hpay.1.2
    have hi := handle.stage.isLt
    change handle.stage.val < I.stageCount at hi
    omega
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hw := window hpay.2
    have hi := handle.stage.isLt
    change handle.stage.val < I.stageCount at hi
    omega
  | stop => exact Or.inl rfl
  | abandon => exact Or.inr rfl

def terminalCursorTail (source : PolicyRule I Seed) (seed : Seed) (history : List (VisibleEvent I)) :
    List (VisibleEvent I) :=
  if historyHalted history then history else history ++ postwriteResponse (source seed history)

theorem measurable_terminalCursorTail [MeasurableSpace Seed] (source : PolicyRule I Seed)
    (hm : MeasurableRule source) :
    Measurable (fun pair : Seed × List (VisibleEvent I) => terminalCursorTail source pair.1 pair.2) :=
  (measurable_of_countable (fun pair : List (VisibleEvent I) × Action I =>
    if historyHalted pair.1 then pair.1 else pair.1 ++ postwriteResponse pair.2)).comp
      (measurable_snd.prodMk hm)

/-- The final active cursor completes in one real action, with the exact
source stop/abandon marker and every earlier paid event retained. -/
theorem terminalCursorTail_eq_completedHistory (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (hl : LegalRule input C mode accounting source)
    (sample : Seed × input.World) (start : ℕ)
    (hc : (run input C mode accounting source sample start).cursor = I.stageCount) :
    completedHistory input C mode accounting source sample =
      some (terminalCursorTail source sample.1 (run input C mode accounting source sample start).history) := by
  obtain ⟨n, _, hp⟩ := run_has_prefix input C mode accounting source hl sample start
  have hhistoryHalt := prefix_historyHalted input C mode accounting source sample.1 _ _ hp
  by_cases hh : (run input C mode accounting source sample start).halted = true
  · have hcompletion := completedHistory_of_halted input C mode accounting source sample start hh
    simpa only [terminalCursorTail, hhistoryHalt, hh, ↓reduceIte] using hcompletion
  · have ha := Bool.eq_false_iff.mpr hh
    rcases currentPayment_terminalCursor_action_cases input C hpay mode accounting source hl sample start ha hc with hs | hs
    · have hnext := run_succ_of_step input C mode accounting source sample start
        (stopState (run input C mode accounting source sample start) false) ha
        (show Step input C mode accounting (worldTapes input sample.2) _ _ _ by rw [hs]; exact .stop _ ha)
      have hcompletion := completedHistory_of_halted input C mode accounting source sample (start + 1)
        (by rw [hnext]; rfl)
      simpa only [hnext, terminalCursorTail, hhistoryHalt, ha, Bool.false_eq_true, ↓reduceIte,
        hs, postwriteResponse, stopState] using hcompletion
    · have hnext := run_succ_of_step input C mode accounting source sample start
        (stopState (run input C mode accounting source sample start) true) ha
        (show Step input C mode accounting (worldTapes input sample.2) _ _ _ by rw [hs]; exact .abandon _ ha)
      have hcompletion := completedHistory_of_halted input C mode accounting source sample (start + 1)
        (by rw [hnext]; rfl)
      simpa only [hnext, terminalCursorTail, hhistoryHalt, ha, Bool.false_eq_true, ↓reduceIte,
        hs, postwriteResponse, stopState] using hcompletion

end PDROC
