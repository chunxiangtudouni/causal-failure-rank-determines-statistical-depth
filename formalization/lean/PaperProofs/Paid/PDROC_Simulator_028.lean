module

public import PaperProofs.Paid.PDROC_Simulator_027
public import PaperProofs.Paid.PDROC_RecordCoupling_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulator_writing_record_report_completed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) = some history)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    (historyReport (simulatorShadow P fee hfee source seed history) stage).map Prod.fst =
      some (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
        (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let guess := (P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape
  let bit := Bool.xor decision (Bool.xor draw.record.orientation guess)
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hwritten : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ↓reduceIte, writeLedger, Function.update_self]
    rfl
  have hframe := completed_simulator_written_report_frame input C.val C.property.1.1 .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) (simulatorSeedDraw P fee hfee source)
    seed history hh (start + n + 1) stage bit hwritten
  have hat := simulator_writing_record_report_at_stop P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hformula := (congrArg (Option.map Prod.fst) hframe).trans hat
  change (historyReport (simulatorShadow P fee hfee source seed history) stage).map Prod.fst =
    some (Bool.xor (input.truthAt world stage) (Bool.xor decision bit)) at hformula
  refine hformula.trans (congrArg some ?_)
  change Bool.xor (input.truthAt world stage)
      (Bool.xor decision (Bool.xor decision (Bool.xor draw.record.orientation guess))) =
    reportedVirtualTruth draw.record.orientation guess (input.truthAt world stage)
  cases decision <;> cases draw.record.orientation <;> cases guess <;> cases input.truthAt world stage <;> decide

end PDROC
