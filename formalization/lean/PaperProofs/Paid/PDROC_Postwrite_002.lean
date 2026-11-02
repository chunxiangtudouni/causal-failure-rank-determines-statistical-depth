module

public import PaperProofs.Paid.PDROC_Postwrite_001
public import PaperProofs.Paid.PDROC_SimulatorProjection_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorStep_terminal_written_shadow {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (cache : SimulatorCache I) (stage : I.Stage)
    (hc : historyCursor cache.seen = stage.val) (hw : historyWritten cache.seen stage ≠ none)
    (abandoned : Bool) :
    (simulatorStep draw seed cache (if abandoned then .abandoned else .stopped)).shadow =
      cache.shadow ++ [if abandoned then .abandoned else .stopped] := by
  cases abandoned <;> simp only [Bool.false_eq_true, ↓reduceIte, simulatorStep, hc,
    hw, simulatorAppend]
  all_goals split_ifs <;> rfl

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- One concrete postwrite simulator step has exactly the source's next
full shadow history. The virtual Prefix is an induction invariant, not a
new assumption in the final representation claim. -/
theorem simulator_postwrite_step_shadow (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s next : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) seed truth tapes n s)
    (ha : s.halted = false) (stage : P.sharedInstance.Stage) (hc : s.cursor = stage.val)
    (hw : s.ledger.written stage ≠ none)
    (vtruth : P.sharedInstance.Stage → Bool) (vtapes : ReviewTapes (P.input fee hfee))
    {vn : ℕ} {vs vnext : State P.sharedInstance}
    (vp : Prefix (P.input fee hfee) C.val .uncapped accounting source seed.1 vtruth vtapes vn vs)
    (va : vs.halted = false) (vh : vs.history = simulatorShadow P fee hfee source seed s.history)
    (vc : vs.cursor = stage.val) (vw : vs.ledger.written stage ≠ none)
    (hs : Step (P.input fee hfee) C.val .uncapped accounting tapes s
      (simulatorRule P fee hfee source seed s.history) next)
    (vstep : Step (P.input fee hfee) C.val .uncapped accounting vtapes vs (source seed.1 vs.history) vnext) :
    simulatorShadow P fee hfee source seed next.history = vnext.history := by
  have heq := simulator_postwrite_rule_eq P fee hfee C accounting source hl seed truth tapes hp ha stage hc hw
    vtruth vtapes vp va vh
  rw [heq, ← vh] at hs
  change vs.history = (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).shadow at vh
  generalize haction : source seed.1 vs.history = action at hs vstep
  have hseen : (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).seen = s.history :=
    simulatorReplay_seen _ _ _
  have hcursor : historyCursor (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).seen = stage.val := by
    rw [hseen, prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp]
    exact hc
  have hwrite : historyWritten (simulatorReplay (simulatorSeedDraw P fee hfee source) seed s.history).seen stage ≠ none := by
    rw [hseen, prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp stage]
    exact hw
  cases vstep with
  | review current live port resources =>
    have hi : current = stage := Fin.ext (live.2.symm.trans vc)
    subst current
    exact (vw port).elim
  | write current bit live port resources =>
    have hi : current = stage := Fin.ext (live.2.symm.trans vc)
    subst current
    exact (vw port).elim
  | allocate handle tool active valid compatible unused unallocated window resources =>
    simp only [reserialAction] at hs
    cases hs
    have hserial : handle.writeSerial = historyWriteSerial vs.history handle.stage :=
      valid.2.1.trans (prefix_historyWriteSerial (P.input fee hfee) C.val .uncapped accounting
        source seed.1 vtruth vtapes vp handle.stage).symm
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.committed (reserialHandle s.history handle) tool])).shadow = vs.history ++ [.committed handle tool]
    rw [simulatorReplay_append_event]
    simp only [simulatorStep, simulatorAppend, ← vh]
    rw [reserialHandle_roundtrip vs.history s.history handle hserial]
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    simp only [reserialAction] at hs
    cases hs
    have hserial : handle.writeSerial = historyWriteSerial vs.history handle.stage :=
      valid.2.1.trans (prefix_historyWriteSerial (P.input fee hfee) C.val .uncapped accounting
        source seed.1 vtruth vtapes vp handle.stage).symm
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.executed (reserialHandle s.history handle) tool])).shadow = vs.history ++ [.executed handle tool]
    rw [simulatorReplay_append_event]
    simp only [simulatorStep, simulatorAppend, ← vh]
    rw [reserialHandle_roundtrip vs.history s.history handle hserial]
  | advance current live written resources =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.advanced current])).shadow = vs.history ++ [.advanced current]
    rw [simulatorReplay_append_event]
    simp only [simulatorStep, simulatorAppend, ← vh]
  | stop active =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.stopped])).shadow = vs.history ++ [.stopped]
    rw [simulatorReplay_append_event]
    simpa only [Bool.false_eq_true, ↓reduceIte, ← vh] using
      simulatorStep_terminal_written_shadow _ _ _ stage hcursor hwrite false
  | abandon active =>
    simp only [reserialAction] at hs
    cases hs
    change (simulatorReplay (simulatorSeedDraw P fee hfee source) seed
      (s.history ++ [.abandoned])).shadow = vs.history ++ [.abandoned]
    rw [simulatorReplay_append_event]
    simpa only [↓reduceIte, ← vh] using
      simulatorStep_terminal_written_shadow _ _ _ stage hcursor hwrite true

end PDROC
