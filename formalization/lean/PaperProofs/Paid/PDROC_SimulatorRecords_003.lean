module

public import PaperProofs.Paid.PDROC_SimulatorRecords_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulatorReviewStateFrom_shadow (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed)
    (stage : P.sharedInstance.Stage) (tape : ((P.input fee hfee).experiment stage).Tape) (s : State P.sharedInstance) (n : ℕ) :
    simulatorShadow P fee hfee source seed
      (simulatorReviewStateFrom (P.input fee hfee) accounting stage tape s n).history =
      simulatorShadow P fee hfee source seed s.history := by
  rw [simulatorReviewStateFrom_history (P.input fee hfee) accounting stage tape s n]
  have he : headReviewHistory (P.input fee hfee) stage tape n =
      (List.ofFn (fun k : Fin n => tape k)).map (fun symbol => .observation stage symbol.val) := by
    simp only [headReviewHistory, List.map_ofFn, Function.comp_def]
  rw [he]
  exact simulatorShadow_append_observations P fee hfee source seed s.history stage _

theorem simulator_writing_record_shadow_at_stop (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hvo : historyObservations (simulatorShadow P fee hfee source seed s.history) stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    simulatorPortView (simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + n + 1)).history) stage =
      (draw.record.observations.map Fin.val, some decision) := by
  let input := P.input fee hfee
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hshadow : simulatorShadow P fee hfee source seed before.history =
      simulatorShadow P fee hfee source seed s.history :=
    simulatorReviewStateFrom_shadow P fee hfee accounting source seed stage tape s n
  have hbefore : historyObservations (simulatorShadow P fee hfee source seed before.history) stage = [] :=
    (congrArg (fun history => historyObservations history stage) hshadow).trans hvo
  have hrec : simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed before.history)) = draw.record := by
    rw [hshadow, hdraw]
    rfl
  change simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
    (simulatorReplay (simulatorSeedDraw P fee hfee source) seed before.history).shadow) = draw.record at hrec
  have hresult := simulatorReplay_writeReport_port (simulatorSeedDraw P fee hfee source) seed before.history
    stage bit (before.ledger.truth stage) before.clock hbefore decision (by rw [hrec, hd])
  rw [hstate]
  simpa only [record, writeResponses, C.property.1.1, ↓reduceIte, writeLedger, List.singleton_append,
    simulatorShadow, hrec] using hresult

end PDROC


