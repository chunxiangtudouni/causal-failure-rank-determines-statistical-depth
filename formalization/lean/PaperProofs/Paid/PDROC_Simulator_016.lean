module

public import PaperProofs.Paid.PDROC_Simulator_015
public import PaperProofs.Paid.PDROC_StageObservables_001
public import PaperProofs.Paid.PDROC_StageObservables_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulator_writing_record_observables_at_stop (P : PaperProofs.Paid.Parameters)
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
    P.actualOrdinaryDecision fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage =
      some (Bool.xor decision (Bool.xor draw.record.orientation
        ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))) ∧
    P.paidRunReviewCount fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = (n : ℕ∞) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let before := simulatorReviewStateFrom input accounting stage tape s n
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have hfields : (reportedWriteLedger C.val before stage bit).written stage = some bit ∧
      (reportedWriteLedger C.val before stage bit).reviews stage = (n : ℕ∞) := by
    have hreview : before.ledger.reviews stage = (n : ℕ∞) :=
      simulatorReviewStateFrom_reviews input accounting stage tape s n hr
    simp only [reportedWriteLedger]
    split_ifs <;> exact ⟨Function.update_self _ _ _, hreview⟩
  have hws : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    exact hfields.1
  have hrs : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.reviews stage = (n : ℕ∞) := by
    rw [hstate]
    exact hfields.2
  exact actualStageObservables_of_written P fee hfee C .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) (start + n + 1) stage bit n hws hrs

/-- A concrete no-decision draw immediately reaches a genuine halted Native
state; its total observed count stays at the original entry count zero. -/
theorem simulator_none_record_observables (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0)
    (hnone : (simulatorDrawRecord (simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed s.history))).decision = none) :
    P.actualOrdinaryDecision fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = none ∧
      P.paidRunReviewCount fee hfee C .uncapped accounting (simulatorRule P fee hfee source) (seed, world) stage = 0 := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  obtain ⟨k, _hk, hp⟩ := run_has_prefix input C.val .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) start
  have hprefix : Prefix input C.val .uncapped accounting actual seed (input.truthAt world) (worldTapes input world) k s := hs0 ▸ hp
  have hhh : historyHalted s.history = false :=
    (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hprefix).trans ha
  have hhc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hprefix).trans hc
  have hhw : historyWritten s.history stage = none :=
    (prefix_historyWritten input C.val .uncapped accounting actual seed _ _ hprefix stage).trans hw
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
  apply actualStageObservables_of_halted_unwritten P fee hfee C .uncapped accounting actual
    (simulatorRule_legal P fee hfee C accounting source) (seed, world) (start + 1) stage 0
  · rw [hhalt]; rfl
  · rw [hhalt]; exact hw
  · rw [hhalt]; exact hr

end PDROC
