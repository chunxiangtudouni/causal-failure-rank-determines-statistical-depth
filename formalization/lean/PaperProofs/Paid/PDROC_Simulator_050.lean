module

public import PaperProofs.Paid.PDROC_Simulator_049

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u}

/-- A finite Good draw for the optional-entry source is precisely a finite
Good draw for the actual source on every real entry. Never-entry requires
no catch and is handled by the original terminal-capture projection. -/
theorem simulator_entry_drawGood_of_optional_stageSample
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World)
    (hgood : let s := simulatorEventualStageSample P fee hfee C accounting source stage sample
      ∃ draw : SimulatorDraw P.sharedInstance,
        simulatorDrawAt P fee hfee (sourceForOptionalHistory source) stage s.1.1.1 s.1.1.2 s.1.2 = some draw ∧
        sourceDrawGuardGood (sourceForOptionalHistory source) stage
          ((s.1.1, draw), recordVirtualTruth P draw.record s.2.2.1 (s.2.1, s.2.2.2))) :
    ∀ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorRule P fee hfee source) stage sample = some entry →
      ∃ draw : SimulatorDraw P.sharedInstance,
        simulatorSeedDraw P fee hfee source sample.1 stage
          (simulatorShadow P fee hfee source sample.1 entry) = some draw ∧
        sourceDrawGuardGood source stage
          (((sample.1.1, simulatorShadow P fee hfee source sample.1 entry), draw),
            recordVirtualTruth P draw.record ((P.input fee hfee).truthAt sample.2 stage)
              (sample.1.2.2 stage, worldTapes (P.input fee hfee) sample.2 stage)) := by
  intro entry he
  dsimp only at hgood
  rw [simulatorEventualStageSample_of_entry P fee hfee C accounting source stage sample entry he] at hgood
  obtain ⟨draw, hd, hg⟩ := hgood
  refine ⟨draw, ?_, ?_⟩
  · change simulatorDrawAt P fee hfee source stage sample.1.1
      (simulatorShadow P fee hfee source sample.1 entry) (sample.1.2.1 stage) = some draw
    exact (simulatorDrawAt_optionalHistory_some P fee hfee source stage sample.1.1
      (simulatorShadow P fee hfee source sample.1 entry)
      (simulatorShadow P fee hfee source sample.1 entry) (sample.1.2.1 stage)).symm.trans hd
  · exact (sourceDrawGuardGood_optionalHistory_some source stage sample.1.1
      (simulatorShadow P fee hfee source sample.1 entry)
      (simulatorShadow P fee hfee source sample.1 entry) draw _).mp hg

end PDROC
