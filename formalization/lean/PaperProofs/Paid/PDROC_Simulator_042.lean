module

public import PaperProofs.Paid.PDROC_Simulator_041

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Actual realization of the full stage kernel on a purely measurable
source packet guard. The source-side conditions contain only the action
shape and three visible permissions; no semantic reachability predicate
or existential virtual Prefix occurs. -/
theorem simulator_stageExit_of_guardGood (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed)
    (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage : P.sharedInstance.Stage)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage.val start (seed, world))
    (draw : SimulatorDraw P.sharedInstance)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).history) = some draw)
    (hshape : (∃ decision, draw.action = .write stage decision) ∨ draw.action = .stop ∨ draw.action = .abandon)
    (hfinite : ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hgood : sourcePostwriteGuardGood source seed.1 stage
      (sourceDrawTerminalHistory stage
        (simulatorShadow P fee hfee source seed
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).history)
        draw (recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
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
          (((seed.1, simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) start).history), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
              (seed.2.2 stage, worldTapes (P.input fee hfee) world stage)) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let s := run input C.val .uncapped accounting actual (seed, world) start
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨ha, hunborn⟩ := firstEntryAt_unborn input C.val .uncapped accounting actual hl
    (seed, world) stage.val start hentry
  obtain ⟨hw, hr⟩ := hunborn stage le_rfl
  obtain ⟨an, _, ap⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) start
  have ho : historyObservations s.history stage = [] := by
    have hlen := prefix_historyObservations_length input C.val .uncapped accounting actual seed _ _ ap stage
    rw [hr] at hlen
    exact List.length_eq_zero_iff.mp (ENat.natCast_inj.mp hlen)
  rcases hshape with ⟨decision, hwrite⟩ | hstop | habandon
  · obtain ⟨n, hn⟩ := hfinite
    exact simulator_writing_stageExit_of_guardGood P fee hfee C accounting source seed world
      start s stage draw decision rfl ha hentry.1 hw hr ho hdraw hwrite n hn hgood
  · obtain ⟨finish, hle, hh, heq⟩ := simulator_terminal_stageExit P fee hfee C accounting source seed world
      start s stage draw false _ rfl ha hentry.1 hw hdraw (by simpa only [Bool.false_eq_true, ↓reduceIte] using hstop)
    exact ⟨finish, hle, Or.inl hh, heq⟩
  · obtain ⟨finish, hle, hh, heq⟩ := simulator_terminal_stageExit P fee hfee C accounting source seed world
      start s stage draw true _ rfl ha hentry.1 hw hdraw habandon
    exact ⟨finish, hle, Or.inl hh, heq⟩

end PDROC
