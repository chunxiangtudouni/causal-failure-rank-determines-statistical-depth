module

public import PaperProofs.Paid.PDROC_SimulatorFlow_003
public import PaperProofs.Paid.PDROC_SimulatorLaw_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The actual simulator's eventual next virtual entry is the same pure
projection of its complete measurable source-kernel exit, on Good. -/
theorem simulator_nextEntry_projection_of_guardGood (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (seed : SimulatorSeed P Seed) (world : (P.input fee hfee).World)
    (start : ℕ) (stage next : P.sharedInstance.Stage) (hnext : next.val = stage.val + 1)
    (hentry : FirstEntryAt (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage.val start (seed, world))
    (draw : SimulatorDraw P.sharedInstance)
    (hdraw : simulatorSeedDraw P fee hfee source seed stage
      (simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) (seed, world) start).history) = some draw)
    (hfinite : ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (seed.2.2 stage)
      (worldTapes (P.input fee hfee) world stage) = (n : ℕ∞))
    (hgood : sourceDrawGuardGood source stage
      (((seed.1, simulatorShadow P fee hfee source seed
        (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
          (seed, world) start).history), draw),
        recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
          (seed.2.2 stage, worldTapes (P.input fee hfee) world stage))) :
    simulatorVirtualEntryGate P fee hfee C accounting source next (seed, world) =
      simulatorNextEntryProjection next
        (sourceDrawStageExit (sourceForOptionalHistory source) stage
          ((((seed.1, some (simulatorShadow P fee hfee source seed
            (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
              (seed, world) start).history)),
            simulatorShadow P fee hfee source seed
              (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
                (seed, world) start).history), draw),
              recordVirtualTruth P draw.record ((P.input fee hfee).truthAt world stage)
                (seed.2.2 stage, worldTapes (P.input fee hfee) world stage))) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  let shadow := simulatorShadow P fee hfee source seed
  have hl := simulatorRule_legal P fee hfee C accounting source
  obtain ⟨offset, hbefore, hexit, hhistory⟩ := simulator_stageExit_minimal_of_sourceDrawGuardGood P fee hfee C accounting source
    seed world start stage hentry draw hdraw hfinite hgood
  obtain ⟨k, _, hp⟩ := run_has_prefix input C.val .uncapped accounting actual hl (seed, world) (start + offset)
  have hprojection := simulatorReplay_sameProjection (simulatorSeedDraw P fee hfee source) seed
    (run input C.val .uncapped accounting actual (seed, world) (start + offset)).history
  have hh : historyHalted (shadow (run input C.val .uncapped accounting actual (seed, world) (start + offset)).history) =
      (run input C.val .uncapped accounting actual (seed, world) (start + offset)).halted :=
    hprojection.2.2.2.2.symm.trans (prefix_historyHalted input C.val .uncapped accounting actual seed _ _ hp)
  have hc : historyCursor (shadow (run input C.val .uncapped accounting actual (seed, world) (start + offset)).history) =
      (run input C.val .uncapped accounting actual (seed, world) (start + offset)).cursor :=
    hprojection.1.symm.trans (prefix_historyCursor input C.val .uncapped accounting actual seed _ _ hp)
  have h := entryHistory_map_projection_of_minimal_stage_exit input C.val .uncapped accounting actual hl
    (seed, world) start offset stage next hnext hentry.1 (fun k hk => (hbefore k hk).2) hexit shadow hh hc seed.1
    (shadow (run input C.val .uncapped accounting actual (seed, world) start).history)
  rw [sourceDrawStageExit_optionalHistory_some]
  rw [show (sourceDrawStageExit source stage
    (((seed.1, shadow (run input C.val .uncapped accounting actual (seed, world) start).history), draw),
      recordVirtualTruth P draw.record (input.truthAt world stage) (seed.2.2 stage, worldTapes input world stage))).2 =
      shadow (run input C.val .uncapped accounting actual (seed, world) (start + offset)).history from
        (congrArg Prod.snd hhistory).symm]
  exact h

omit [MeasurableSpace Seed] in
theorem simulator_nextEntry_projection_of_no_prior_entry (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (stage next : P.sharedInstance.Stage) (hle : stage.val ≤ next.val)
    (hnone : (simulatorVirtualEntryGate P fee hfee C accounting source stage sample).2 = none)
    (exit : List (VisibleEvent P.sharedInstance)) :
    simulatorVirtualEntryGate P fee hfee C accounting source next sample =
      simulatorNextEntryProjection next ((sample.1.1, none), exit) := by
  have ha : entryHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage sample = none := by
    cases he : entryHistory (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) stage sample with
    | none => rfl
    | some history =>
      simp only [simulatorVirtualEntryGate, simulatorVirtualEntry, he, Option.map_some, reduceCtorEq] at hnone
  exact entryHistory_map_projection_of_no_prior_entry (P.input fee hfee) C.val .uncapped accounting
    (simulatorRule P fee hfee source) (simulatorRule_legal P fee hfee C accounting source) sample stage next hle ha
    (simulatorShadow P fee hfee source sample.1) sample.1.1 exit

end PDROC


