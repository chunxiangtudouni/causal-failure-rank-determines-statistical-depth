module

public import PaperProofs.Paid.PDROC_Postwrite_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- A measurable public permission on the generated shadow is sufficient
for the concrete postwrite guard. No existential source world or virtual
Prefix is conditioned upon or required in this interface. -/
theorem simulator_postwrite_rule_eq_of_historyAllowsAction
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) seed truth tapes n s)
    (ha : s.halted = false) (stage : P.sharedInstance.Stage) (hc : s.cursor = stage.val)
    (hw : s.ledger.written stage ≠ none)
    (hvallow : historyAllowsAction (simulatorShadow P fee hfee source seed s.history)
      (source seed.1 (simulatorShadow P fee hfee source seed s.history))) :
    simulatorRule P fee hfee source seed s.history =
      reserialAction s.history (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) := by
  have hproj := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed s.history
  have hallow := historyAllowsAction_reserial_transport s.history (simulatorShadow P fee hfee source seed s.history)
    (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) hproj.1 hproj.2.2.2.1
    (simulatorShadow_validHandle_prefix P fee hfee C .uncapped accounting source
      (simulatorRule P fee hfee source) seed truth tapes hp)
    (prefix_simulatorCommitments_reserial (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp (simulatorSeedDraw P fee hfee source) seed)
    (prefix_simulatorExecutions_reserial (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) seed truth tapes hp (simulatorSeedDraw P fee hfee source) seed) hvallow
  have hhalt := prefix_historyHalted (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp
  have hcursor := prefix_historyCursor (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp
  have hwrite := prefix_historyWritten (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) seed truth tapes hp stage
  have hcandidate : simulatorCandidate P fee hfee source seed s.history =
      reserialAction s.history (fun _ bit => bit) (source seed.1 (simulatorShadow P fee hfee source seed s.history)) := by
    have hstage : simulatorStageAt s.history = some stage := by
      simp only [simulatorStageAt, hcursor, hc, stage.isLt, ↓reduceDIte]
    simp only [simulatorCandidate, simulatorCandidateAtCache, simulatorCandidateFromData, hhalt, ha,
      Bool.false_eq_true, ↓reduceIte, hstage, hwrite, hw, simulatorShadow]
  simp only [simulatorRule, hcandidate, hallow, ↓reduceIte]

end PDROC
