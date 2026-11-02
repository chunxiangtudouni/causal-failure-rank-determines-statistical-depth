module

public import PaperProofs.Paid.PDROC_Simulator_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- A finite endpoint stop is realized by the actual write transition and
its genuine early-report response, from the original actual starting state. -/
theorem simulator_run_write_at_endpoint (P : PaperProofs.Paid.Parameters)
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
    let tape := worldTapes (P.input fee hfee) world stage
    let before := simulatorReviewStateFrom (P.input fee hfee) accounting stage tape s n
    let bit := Bool.xor decision (Bool.xor draw.record.orientation
      ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
    run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) (start + n + 1) =
      record accounting before (.write stage bit) (writeResponses C.val before stage bit)
        (reportedWriteLedger C.val before stage bit) before.cursor false := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  have ha0 : (run input C.val .uncapped accounting actual (seed, world) start).halted = false :=
    (congrArg State.halted hs0).trans ha
  have hc0 : (run input C.val .uncapped accounting actual (seed, world) start).cursor = stage.val :=
    (congrArg State.cursor hs0).trans hc
  have hw0 : (run input C.val .uncapped accounting actual (seed, world) start).ledger.written stage = none :=
    (congrArg (fun st => st.ledger.written stage) hs0).trans hw
  have hr0 : (run input C.val .uncapped accounting actual (seed, world) start).ledger.reviews stage = 0 :=
    (congrArg (fun st => st.ledger.reviews stage) hs0).trans hr
  have ho0 : historyObservations (run input C.val .uncapped accounting actual (seed, world) start).history stage = [] :=
    (congrArg (fun st => historyObservations st.history stage) hs0).trans ho
  have hdraw0 : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed (run input C.val .uncapped accounting actual (seed, world) start).history) = some draw :=
    (congrArg (fun st => simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed st.history)) hs0).trans hdraw
  have hreview := simulator_run_eq_reviewStateFrom P fee hfee C accounting source seed world start stage draw decision
    ha0 hc0 hw0 hr0 ho0 hdraw0 hd n (by rw [hs])
  have heq : run input C.val .uncapped accounting actual (seed, world) (start + n) = before := by
    simpa only [hs0] using hreview
  have haction : actual seed before.history = .write stage bit :=
    (congrArg (actual seed) (simulatorReviewStateFrom_history input accounting stage tape s n)).trans
      (simulatorRule_on_endpoint_word_at_stop P fee hfee source seed s.history stage draw decision hhh hhc hhw ho hdraw hd tape n hs)
  have hbactive : before.halted = false := simulatorReviewStateFrom_active input accounting stage tape s n ha
  have hbw : before.ledger.written stage = none :=
    (congrFun (simulatorReviewStateFrom_written input accounting stage tape s n) stage).trans hw
  have hstep : Step input C.val .uncapped accounting (worldTapes input world) before (.write stage bit)
      (record accounting before (.write stage bit) (writeResponses C.val before stage bit)
        (reportedWriteLedger C.val before stage bit) before.cursor false) :=
    .write before stage bit ⟨hbactive, (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc⟩ hbw (Or.inl rfl)
  apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) (start + n) _
  · exact (congrArg State.halted heq).trans hbactive
  · rw [heq, haction]
    exact hstep

end PDROC
