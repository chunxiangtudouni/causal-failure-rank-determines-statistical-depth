module

public import PaperProofs.Paid.PDROC_Simulator_034

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The genuine actual stage exit realizes the complete deterministic source
stage kernel. Its prefix condition is a genuine source run at the selected
terminal packet, supplied by the source-entry construction. -/
theorem simulator_writing_stageExit_of_source_terminal (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (hl : LegalRule (P.input fee hfee) C.val .uncapped accounting source)
    (seed : SimulatorSeed P Seed) (world vworld : (P.input fee hfee).World)
    (start : ℕ) (s : State P.sharedInstance) (stage : P.sharedInstance.Stage)
    (draw : SimulatorDraw P.sharedInstance) (decision : Bool)
    (hs0 : run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start = s)
    (ha : s.halted = false) (hc : s.cursor = stage.val) (hw : s.ledger.written stage = none)
    (hr : s.ledger.reviews stage = 0) (ho : historyObservations s.history stage = [])
    (hdraw : simulatorSeedDraw P fee hfee source seed stage (simulatorShadow P fee hfee source seed s.history) = some draw)
    (haction : draw.action = .write stage decision) (n : ℕ)
    (hs : (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (vstart : ℕ)
    (hvpacket : (run (P.input fee hfee) C.val .uncapped accounting source (seed.1, vworld) vstart).history =
      sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw
        (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)))
    (hvc : (run (P.input fee hfee) C.val .uncapped accounting source
      (seed.1, vworld) vstart).cursor = stage.val)
    (hvw : (run (P.input fee hfee) C.val .uncapped accounting source
      (seed.1, vworld) vstart).ledger.written stage = some decision) :
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
  have hpacket := simulator_writing_record_shadow_packet P fee hfee C accounting source seed world start s stage draw decision
    hs0 ha hc hw hr ho hdraw haction n hs
  have hsync := hpacket.trans hvpacket.symm
  obtain ⟨exit, _, hexit, hfinal⟩ := simulator_postwrite_exit_of_source_run P fee hfee C accounting source hl
    seed world vworld (start + n + 1) vstart stage bit decision haw hvw hvc hsync
  refine ⟨start + n + 1 + exit, by omega, hexit, ?_⟩
  dsimp only [sourceDrawStageExit]
  apply congrArg (Prod.mk seed.1)
  change simulatorShadow P fee hfee source seed
      (run input C.val .uncapped accounting actual (seed, world) (start + n + 1 + exit)).history =
    postwriteStageTrace source seed.1 stage
      (sourceDrawTerminalHistory stage (simulatorShadow P fee hfee source seed s.history) draw
        (recordVirtualTruth P draw.record (input.truthAt world stage) (seed.2.2 stage, tape))) 3
  exact hfinal.trans (congrArg (fun history => postwriteStageTrace source seed.1 stage history 3) hvpacket)

end PDROC
