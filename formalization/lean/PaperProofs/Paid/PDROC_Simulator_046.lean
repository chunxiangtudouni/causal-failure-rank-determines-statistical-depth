module

public import PaperProofs.Paid.PDROC_Simulator_045

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- The actual completed shadow at cursor N is the source's measurable
terminal tail. Only an active-history public guard is needed, with no
semantic source reachability condition and no truth coordinate in Seed. -/
theorem simulator_terminalCursor_shadowCompletedHistory
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) (start : ℕ)
    (hc : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      sample start).cursor = P.sharedInstance.stageCount)
    (hallow : historyHalted (simulatorShadow P fee hfee source sample.1
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample start).history) = false →
      historyAllowsAction (simulatorShadow P fee hfee source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample start).history)
        (source sample.1.1 (simulatorShadow P fee hfee source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample start).history))) :
    P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) sample =
      some (terminalCursorTail source sample.1.1 (simulatorShadow P fee hfee source sample.1
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample start).history)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let history := (run input C.val .uncapped accounting actual sample start).history
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl sample start
  have hcursor : historyCursor history = P.sharedInstance.stageCount :=
    (prefix_historyCursor input C.val .uncapped accounting actual sample.1 _ _ ap).trans hc
  have hproj := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) sample.1 history
  have hcShadow : historyCursor (simulatorShadow P fee hfee source sample.1 history) = P.sharedInstance.stageCount :=
    hproj.1.symm.trans hcursor
  have hcompletion := terminalCursorTail_eq_completedHistory input C.val C.property .uncapped accounting actual hl sample start hc
  change (completedHistory input C.val .uncapped accounting actual sample).map
      (simulatorShadow P fee hfee source sample.1) = _
  rw [hcompletion]
  simp only [Option.map_some]
  apply congrArg some
  change simulatorShadow P fee hfee source sample.1 (terminalCursorTail actual sample.1 history) =
    terminalCursorTail source sample.1.1 (simulatorShadow P fee hfee source sample.1 history)
  by_cases hh : historyHalted history = true
  · have hvh : historyHalted (simulatorShadow P fee hfee source sample.1 history) = true := hproj.2.2.2.2.symm.trans hh
    simp only [terminalCursorTail, hh, hvh, ↓reduceIte]
  · have ha : historyHalted history = false := Bool.eq_false_iff.mpr hh
    have hva : historyHalted (simulatorShadow P fee hfee source sample.1 history) = false := hproj.2.2.2.2.symm.trans ha
    have hvallow := hallow hva
    have heq : actual sample.1 history = source sample.1.1 (simulatorShadow P fee hfee source sample.1 history) :=
      simulatorRule_terminalCursor_of_historyAllowsAction P fee hfee source sample.1 history ha hcursor hvallow
    have hcases := historyAllowsAction_terminalCursor_cases _ hcShadow _ hvallow
    simp only [terminalCursorTail, ha, hva, Bool.false_eq_true, ↓reduceIte, heq]
    rcases hcases with hs | hs
    · rw [hs]
      simpa only [postwriteResponse, Bool.false_eq_true, ↓reduceIte, simulatorShadow] using
        simulatorReplay_terminal_outOfRange (simulatorSeedDraw P fee hfee source) sample.1 history false hcursor
    · rw [hs]
      simpa only [postwriteResponse, ↓reduceIte, simulatorShadow] using
        simulatorReplay_terminal_outOfRange (simulatorSeedDraw P fee hfee source) sample.1 history true hcursor

end PDROC
