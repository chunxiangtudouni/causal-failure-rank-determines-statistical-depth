module

public import PaperProofs.Paid.PDROC_Simulator_026
public import PaperProofs.Paid.PDROC_SimulatorRecords_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

theorem simulatorReplay_writeReport_truth {SimSeed : Type*}
    (draw : SimSeed → I.Stage → List (VisibleEvent I) → Option (SimulatorDraw I))
    (seed : SimSeed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (bit truth : Bool) (serial : ℕ) (decision : Bool)
    (hd : (simulatorDrawRecord (draw seed stage (simulatorReplay draw seed history).shadow)).decision = some decision) :
    (historyReport (simulatorReplay draw seed
      (history ++ [.wrote stage bit serial, .report stage truth serial])).shadow stage).map Prod.fst =
      some (Bool.xor truth (Bool.xor decision bit)) := by
  rw [show history ++ [.wrote stage bit serial, .report stage truth serial] =
    (history ++ [.wrote stage bit serial]) ++ [.report stage truth serial] by simp]
  rw [simulatorReplay_append_event, simulatorReplay_append_event]
  simp only [simulatorStep, simulatorAppend, Function.update_self, Option.getD_some]
  rw [hd]
  simp only [Option.getD_some]
  simp [historyReport, historyWritten, historyWrite, historyWriteSerial,
    List.filterMap_append, eventWrite, eventReport]

universe u
variable {Seed : Type u}

theorem simulator_writing_record_report_at_stop (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    let endpoint := (P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage)
    let actualBit := Bool.xor decision (Bool.xor draw.record.orientation endpoint)
    (historyReport (simulatorShadow P fee hfee source seed
      (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) (start + n + 1)).history) stage).map Prod.fst =
      some (Bool.xor ((P.input fee hfee).truthAt world stage) (Bool.xor decision actualBit)) := by
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
  have hrec : simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed before.history)) = draw.record := by
    rw [hshadow, hdraw]
    rfl
  have htruth : before.ledger.truth stage = input.truthAt world stage := by
    have hreview := simulator_run_eq_reviewStateFrom P fee hfee C accounting source seed world start stage draw decision
      (by simpa only [hs0] using ha) (by simpa only [hs0] using hc)
      (by simpa only [hs0] using hw) (by simpa only [hs0] using hr)
      (by simpa only [hs0] using ho) (by simpa only [hs0] using hdraw) hd n (by rw [hs])
    have hb : run input C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) (start + n) = before := by
      simpa only [hs0] using hreview
    exact (congrArg (fun st => st.ledger.truth stage) hb).symm.trans
      (congrFun (run_truth input C.val .uncapped accounting (simulatorRule P fee hfee source)
        (simulatorRule_legal P fee hfee C accounting source) (seed, world) (start + n)) stage)
  change simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
    (simulatorReplay (simulatorSeedDraw P fee hfee source) seed before.history).shadow) = draw.record at hrec
  have hresult := simulatorReplay_writeReport_truth (simulatorSeedDraw P fee hfee source) seed before.history
    stage bit (before.ledger.truth stage) before.clock decision (by rw [hrec, hd])
  rw [hstate]
  simp only [record, writeResponses, C.property.1.1, ↓reduceIte, writeLedger, List.singleton_append]
  change (historyReport (simulatorShadow P fee hfee source seed
    (before.history ++ [.wrote stage bit before.clock, .report stage (before.ledger.truth stage) before.clock])) stage).map Prod.fst =
      some (Bool.xor (input.truthAt world stage) (Bool.xor decision bit))
  exact hresult.trans (congrArg some (congrArg (fun truth => Bool.xor truth (Bool.xor decision bit)) htruth))

end PDROC
