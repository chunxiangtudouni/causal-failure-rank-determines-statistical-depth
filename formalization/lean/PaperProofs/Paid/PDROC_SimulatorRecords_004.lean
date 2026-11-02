module

public import PaperProofs.Paid.PDROC_SimulatorRecords_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

theorem simulator_none_record_shadow_completed (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (history : List (VisibleEvent P.sharedInstance))
    (hh : completedHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) (seed, world) = some history)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hnone : (simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history))).decision = none) :
    simulatorPortView (simulatorShadow P fee hfee source seed history) stage =
      ((simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
        (simulatorShadow P fee hfee source seed s.history))).observations.map Fin.val, none) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
  have hf := prefix_simulator_unwritten_port_fresh input C.val .uncapped accounting actual seed _ _ hprefix ha stage hw
    (simulatorSeedDraw P fee hfee source) seed
  have hvw : historyWritten (simulatorShadow P fee hfee source seed s.history) stage = none := by
    simp only [simulatorShadow, historyWritten, hf.2, Option.map_none]
  have ht := simulatorRule_prewrite_none_terminal P fee hfee source seed s.history stage hhh hhc hhw hnone
  have hwitness : ∃ abandon : Bool,
      run input C.val .uncapped accounting actual (seed, world) (start + 1) = stopState s abandon := by
    rcases ht with hstop | habandon
    · refine ⟨false, ?_⟩
      apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) start _
      · exact (congrArg State.halted hs0).trans ha
      · rw [hs0]
        have hsaction : actual seed s.history = .stop := hstop
        rw [hsaction]
        exact .stop s ha
    · refine ⟨true, ?_⟩
      apply run_succ_of_step input C.val .uncapped accounting actual (seed, world) start _
      · exact (congrArg State.halted hs0).trans ha
      · rw [hs0]
        have hsaction : actual seed s.history = .abandon := habandon
        rw [hsaction]
        exact .abandon s ha
  obtain ⟨abandon, hhalt⟩ := hwitness
  have hhfinal := completedHistory_eq_history_of_halted input C.val .uncapped accounting actual
    (seed, world) history hh (start + 1) (by rw [hhalt]; rfl)
  rw [hhfinal, hhalt]
  exact simulatorReplay_terminal_port (simulatorSeedDraw P fee hfee source) seed s.history stage abandon hhc hhw hf.1 hvw

theorem simulator_writing_record_shadow_completed (P : PaperProofs.Paid.Parameters)
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
    (hvo : historyObservations (simulatorShadow P fee hfee source seed s.history) stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (hd : draw.record.decision = some decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞)) :
    simulatorPortView (simulatorShadow P fee hfee source seed history) stage =
      (draw.record.observations.map Fin.val, some decision) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hwritten : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ↓reduceIte, writeLedger, Function.update_self]
    rfl
  have hframe := completed_simulator_written_port_frame input C.val C.property.1.1 .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) (simulatorSeedDraw P fee hfee source)
    seed history hh (start + n + 1) stage bit hwritten
  exact hframe.trans (simulator_writing_record_shadow_at_stop P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hvo hdraw hd n hs)

end PDROC

