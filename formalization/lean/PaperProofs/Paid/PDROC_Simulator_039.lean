module

public import PaperProofs.Paid.PDROC_Simulator_038
public import PaperProofs.Paid.PDROC_Postwrite_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem historyValidHandle_writeSerial {history : List (VisibleEvent I)} {handle : MismatchHandle I}
    (h : historyValidHandle history handle) : handle.writeSerial = historyWriteSerial history handle.stage := by
  unfold historyValidHandle at h
  cases hr : historyReport history handle.stage with
  | none => simp only [hr] at h
  | some report =>
    cases report with
    | mk truth serial => simp only [hr] at h; exact h.2.2.symm

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- A public, measurable permission suffices for the exact actual next
shadow. No genuine source Prefix or existential source world is used. -/
theorem simulator_postwrite_step_shadow_of_historyAllowsAction
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s next : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) seed truth tapes n s)
    (ha : s.halted = false) (stage : P.sharedInstance.Stage) (hc : s.cursor = stage.val)
    (hw : s.ledger.written stage ≠ none)
    (hvallow : historyAllowsAction (simulatorShadow P fee hfee source seed s.history)
      (source seed.1 (simulatorShadow P fee hfee source seed s.history)))
    (hs : Step (P.input fee hfee) C.val .uncapped accounting tapes s
      (simulatorRule P fee hfee source seed s.history) next) :
    simulatorShadow P fee hfee source seed next.history =
      postwriteStageStep source seed.1 stage (simulatorShadow P fee hfee source seed s.history) := by
  have heq := simulator_postwrite_rule_eq_of_historyAllowsAction P fee hfee C accounting source seed truth tapes
    hp ha stage hc hw hvallow
  have hproj := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed s.history
  have hhalt : historyHalted (simulatorShadow P fee hfee source seed s.history) = false :=
    hproj.2.2.2.2.symm.trans ((prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp).trans ha)
  have hcursor : historyCursor (simulatorShadow P fee hfee source seed s.history) = stage.val :=
    hproj.1.symm.trans ((prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp).trans hc)
  have hwrite : historyWritten (simulatorShadow P fee hfee source seed s.history) stage ≠ none := by
    intro hn
    exact hw ((prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp stage).symm.trans ((hproj.2.2.2.1 stage).mpr hn))
  have hpost : postwriteStageStep source seed.1 stage (simulatorShadow P fee hfee source seed s.history) =
      simulatorShadow P fee hfee source seed s.history ++
        postwriteResponse (source seed.1 (simulatorShadow P fee hfee source seed s.history)) := by
    simp only [postwriteStageStep, hhalt, Bool.false_eq_true, ↓reduceIte, hcursor]
  have hseenCursor : historyCursor (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).seen = stage.val := by
    simpa only [simulatorReplay_seen] using
      (prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) seed truth tapes hp).trans hc
  have hseenWritten : historyWritten (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).seen stage ≠ none := by
    simpa only [simulatorReplay_seen, prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp] using hw
  rw [hpost]
  rw [heq] at hs
  generalize haction : source seed.1 (simulatorShadow P fee hfee source seed s.history) = action at hs hvallow ⊢
  cases action with
  | review current =>
    have hi : current = stage := Fin.ext (hvallow.1.symm.trans hcursor)
    subst current
    exact (hwrite hvallow.2).elim
  | write current bit =>
    have hi : current = stage := Fin.ext (hvallow.1.symm.trans hcursor)
    subst current
    exact (hwrite hvallow.2).elim
  | allocate handle tool =>
    have hserial := historyValidHandle_writeSerial hvallow.2.1
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.committed (reserialHandle s.history handle) tool])).shadow =
        (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow ++ [.committed handle tool]
    rw [simulatorReplay_append_event]
    simp only [simulatorStep, simulatorAppend]
    rw [reserialHandle_roundtrip (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow s.history handle hserial]
  | execute handle tool =>
    have hserial := historyValidHandle_writeSerial hvallow.2.1
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.executed (reserialHandle s.history handle) tool])).shadow =
        (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow ++ [.executed handle tool]
    rw [simulatorReplay_append_event]
    simp only [simulatorStep, simulatorAppend]
    rw [reserialHandle_roundtrip (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow s.history handle hserial]
  | advance current =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.advanced current])).shadow =
        (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow ++ [.advanced current]
    rw [simulatorReplay_append_event]
    rfl
  | stop =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.stopped])).shadow =
        (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow ++ [.stopped]
    rw [simulatorReplay_append_event]
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      simulatorStep_terminal_written_shadow _ _ _ stage hseenCursor hseenWritten false
  | abandon =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.abandoned])).shadow =
        (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow ++ [.abandoned]
    rw [simulatorReplay_append_event]
    simpa only [↓reduceIte] using
      simulatorStep_terminal_written_shadow _ _ _ stage hseenCursor hseenWritten true

end PDROC
