module

public import PaperProofs.Paid.PDROC_Simulator_047

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The exact eventual exit RV catches a genuine full actual-run shadow.
No semantic source support set is involved in this path identification. -/
theorem simulatorEventualStageExit_catch_of_guardGood
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source) stage sample = some entry)
    (draw : SimulatorDraw P.sharedInstance)
    (hd : simulatorSeedDraw P fee hfee source sample.1 stage
      (simulatorShadow P fee hfee source sample.1 entry) = some draw)
    (hfinite : ∃ n : ℕ, (P.binarySymmetric.rocEndpointTest draw.record.level).rule.stop (sample.1.2.2 stage)
      (worldTapes (P.input fee hfee) sample.2 stage) = (n : ℕ∞))
    (hgood : sourceDrawGuardGood source stage
      (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
        recordVirtualTruth P draw.record ((P.input fee hfee).truthAt sample.2 stage)
          (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage))) :
    ∃ clock : ℕ,
      (simulatorEventualStageExit P fee hfee C accounting source stage sample).2 =
        some (simulatorShadow P fee hfee source sample.1
          (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample clock).history) ∧
      ((run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample clock).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source) sample clock).cursor) := by
  let input := P.input fee hfee
  let actual := simulatorRule P fee hfee source
  obtain ⟨start, hc, hbefore, hh⟩ := (entryHistory_some_iff input C.val .uncapped accounting actual stage sample entry).mp he
  have hentry : FirstEntryAt input C.val .uncapped accounting actual stage.val start sample := ⟨hc, hbefore⟩
  have hd' : simulatorSeedDraw P fee hfee source sample.1 stage
      (simulatorShadow P fee hfee source sample.1 (run input C.val .uncapped accounting actual sample start).history) = some draw := by
    rw [hh]
    exact hd
  have hg' : sourceDrawGuardGood source stage
      (((sample.1.1, simulatorShadow P fee hfee source sample.1 (run input C.val .uncapped accounting actual sample start).history), draw),
        recordVirtualTruth P draw.record (input.truthAt sample.2 stage)
          (sample.1.2.2 stage, worldTapes input sample.2 stage)) := by
    rw [hh]
    exact hgood
  obtain ⟨offset, _, hexit, hkernel⟩ := simulator_stageExit_minimal_of_sourceDrawGuardGood P fee hfee C accounting source
    sample.1 sample.2 start stage hentry draw hd' hfinite hg'
  have hh' : (run (P.input fee hfee) C.val .uncapped accounting (simulatorRule P fee hfee source)
      (sample.1, sample.2) start).history = entry := hh
  rw [hh'] at hkernel
  have hkernel' : (sourceDrawStageExit source stage
      (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
        recordVirtualTruth P draw.record (input.truthAt sample.2 stage)
          (sample.1.2.2 stage, worldTapes input sample.2 stage))).2 =
      simulatorShadow P fee hfee source sample.1 (run input C.val .uncapped accounting actual sample (start + offset)).history := by
    exact (congrArg Prod.snd hkernel).symm
  have hrv := congrArg Prod.snd (simulatorEventualStageExit_of_entry_draw P fee hfee C accounting source stage sample entry he draw hd)
  refine ⟨start + offset, hrv.trans (congrArg some hkernel'), ?_⟩
  rcases hexit with hh | hc
  · exact Or.inl hh
  · exact Or.inr (by rw [hc]; omega)

end PDROC
