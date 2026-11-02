module

public import PaperProofs.Paid.PDROC_Simulator_040
public import PaperProofs.Paid.PDROC_SimulatorLaw_009

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The complete actual writing-stage exit is determined by the measurable
three-guard condition on the selected source packet. No source-world or
source-Prefix witness is needed in this realization interface. -/
theorem simulator_writing_stageExit_of_guardGood (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = .write stage decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hgood : sourcePostwriteGuardGood source seed.1 stage
      (sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw
        (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)))) :
    ∃ finish : ℕ, start ≤ finish ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
        (seed, world) finish).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) finish).cursor) ∧
      (seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) finish).history) =
        sourceDrawStageExit source stage
          (((seed.1, simulatorShadow P fee hfee source seed s.history), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
              (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let tape := worldTapes input world stage
  let bit := Bool.xor decision (Bool.xor draw.record.orientation
    ((P.binarySymmetric.rocEndpointTest draw.record.level).rule.decision (seed.2.2 stage) tape))
  have hd : draw.record.decision = some decision := by
    have hd := (simulatorSeedDraw_some_spec P fee hfee source seed stage _ draw hdraw).1
    simpa only [haction, optionWriteBit] using hd
  have hstate := simulator_run_write_at_endpoint P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw hd n hs
  have haw : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).ledger.written stage = some bit := by
    rw [hstate]
    simp only [record, reportedWriteLedger, C.property.1.1, ↓reduceIte, writeLedger, Function.update_self]
    rfl
  have hac : (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).cursor = stage.val := by
    rw [hstate]
    exact (simulatorReviewStateFrom_cursor input accounting stage tape s n).trans hc
  have hpacket := simulator_writing_record_shadow_packet P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw haction n hs
  have hgood' : sourcePostwriteGuardGood source seed.1 stage
      (simulatorShadow P fee hfee source seed
        (run input C.val .uncapped accounting actual (seed, world) (start + n + 1)).history) := by
    rw [hpacket]
    exact hgood
  obtain ⟨exit, _, _, hexit, hfinal⟩ := simulator_postwrite_exit_of_guardGood P fee hfee C accounting source
    seed world (start + n + 1) stage bit hac haw hgood'
  refine ⟨start + n + 1 + exit, by omega, hexit, ?_⟩
  rw [hpacket] at hfinal
  exact congrArg (Prod.mk seed.1) hfinal

end PDROC
