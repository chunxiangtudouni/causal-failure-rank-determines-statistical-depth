module

public import PaperProofs.Paid.PDROC_SimulatorFlow_005
public import PaperProofs.Paid.PDROC_SimulatorLaw_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem sourceEventualStageExitSome_seed (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World) :
    (sourceEventualStageExitSome P fee hfee C accounting source stage sample).1 =
      (sample.1, entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample) := by
  rfl

/-- Thin genuine source-exit witness for terminal capture. The mathematical
reported-draw kernel is an actual complete Native exit history on each real
entry and finite local draw, including stop and abandon. -/
theorem sourceEventualStageExitSome_actual_exit_of_finite (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (stage : P.sharedInstance.Stage) (sample : Seed × (P.input fee hfee).World)
    (hs : (simulatorLocalTest P fee hfee (sourceForOptionalHistory source.rule)
      (measurable_sourceForOptionalHistory source.rule source.measurable_rule) stage).rule.stop
        (sourceEventualStageSample P fee hfee C accounting source stage sample).1
        (sourceEventualStageSample P fee hfee C accounting source stage sample).2.2 ≠ ⊤)
    (entry : List (VisibleEvent P.sharedInstance))
    (he : entryHistory (P.input fee hfee) C.val .uncapped accounting source.rule stage sample = some entry) :
    ∃ clock : ℕ,
      (sourceEventualStageExitSome P fee hfee C accounting source stage sample).2 =
        some (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).history ∧
      ((run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).halted = true ∨
        stage.val < (run (P.input fee hfee) C.val .uncapped accounting source.rule sample clock).cursor) := by
  obtain ⟨start, draw, hfirst, hhistory, hd, hreport⟩ :=
    sourceEventualReportedDraw_source_realization_of_finite P fee hfee C accounting source stage sample hs entry he
  obtain ⟨offset, _, hexit, hstage⟩ := firstEntry_sourceDrawStageExit_minimal P fee hfee C accounting
    source.rule source.legal sample start stage hfirst draw hd
  have hstageHistory := congrArg Prod.snd hstage
  rw [hhistory] at hstageHistory
  refine ⟨start + offset, ?_, ?_⟩
  · change some ((sourceDrawStageExit (sourceForOptionalHistory source.rule) stage
      (sourceEventualReportedDraw P fee hfee C accounting source stage sample)).2) = _
    rw [hreport, sourceDrawStageExit_optionalHistory_some]
    exact congrArg some hstageHistory.symm
  · rcases hexit with hh | hc
    · exact Or.inl hh
    · exact Or.inr (by omega)

end PDROC
