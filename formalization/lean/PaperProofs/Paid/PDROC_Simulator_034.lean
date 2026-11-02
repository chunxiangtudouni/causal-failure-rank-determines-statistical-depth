module

public import PaperProofs.Paid.PDROC_Simulator_033
public import PaperProofs.Paid.PDROC_SimulatorLaw_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorReviewStateFrom_truth (input : StatisticalInput I) (accounting : NormalAccounting I)
    (stage : I.Stage) (tape : (input.experiment stage).Tape) (s : State I) (n : ℕ) :
    (simulatorReviewStateFrom input accounting stage tape s n).ledger.truth = s.ledger.truth := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

universe u
variable {Seed : Type u}

/-- At the actual endpoint write, the entire shadow is the source's selected
terminal packet, with virtual truth reconstructed from the genuine report. -/
theorem simulator_writing_record_shadow_packet (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = .write stage decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + n + 1)).history =
      sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw
        (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let guess := (P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape
  let bit := Bool.xor decision (Bool.xor draw.record.orientation guess)
  have hd : draw.record.decision = some decision := by
    have hd := (simulatorSeedDraw_some_spec P fee hfee source seed stage _ draw hdraw).1
    simpa only [haction, optionWriteBit] using hd
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hshadow : simulatorShadow P fee hfee source seed before.history =
      simulatorShadow P fee hfee source seed s.history :=
    simulatorReviewStateFrom_shadow P fee hfee accounting source seed stage tape s n
  have hrec : simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed before.history)) = draw.record := by
    rw [hshadow, hdraw]
    rfl
  have htruth : before.ledger.truth stage = input.truthAt world stage := by
    have ht : s.ledger.truth = input.truthAt world :=
      (congrArg (fun st => st.ledger.truth) hs0).symm.trans
        (run_truth input C.val .uncapped accounting (simulatorRule P fee hfee source)
          (simulatorRule_legal P fee hfee C accounting source) (seed, world) start)
    exact congrFun ((simulatorReviewStateFrom_truth input accounting stage tape s n).trans ht) stage
  have hflip : Bool.xor (before.ledger.truth stage) (Bool.xor decision bit) =
      recordVirtualTruth P draw.record (input.truthAt world stage) (seed.2.2 stage, tape) := by
    rw [htruth]
    change Bool.xor (input.truthAt world stage)
        (Bool.xor decision (Bool.xor decision (Bool.xor draw.record.orientation guess))) =
      reportedVirtualTruth draw.record.orientation guess (input.truthAt world stage)
    cases decision <;> cases draw.record.orientation <;> cases guess <;> cases input.truthAt world stage <;> decide
  have hfull := simulatorReplay_writeReport_shadow (simulatorSeedDraw P fee hfee source) seed before.history
    stage bit (before.ledger.truth stage) before.clock
  dsimp only at hfull
  simp only [simulatorShadow] at hrec hshadow hfull
  rw [hrec, hd, Option.getD_some, hflip, hshadow] at hfull
  rw [hstate, sourceDrawTerminalHistory_write stage _ draw _ decision haction]
  simpa only [record, writeResponses, C.property.1.1, ↓reduceIte, writeLedger,
    List.singleton_append, simulatorShadow] using hfull

end PDROC
