module

public import PaperProofs.Retained.PRet_SuccessPreservation_037

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNativeRearrangement038

open Common Common.Native MeasureTheory PRetDelayedPolicy010 PRetDelayedTerminalOnly011
open PRetReplayConsequences017 PRetPathwiseDomination024 PRetSuccessPreservation037

universe u

variable {I : Instance}

/-- Original R02, with every original Seed universe, real full-policy source,
all paths' actual variable fees and all probability laws. -/
theorem native_rearrangement (input : StatisticalInput I) : NativeRearrangement.{u} input := by
  intro C hretained accounting mode Seed m
  let : MeasurableSpace Seed := m
  intro source
  refine ⟨policy input C hretained accounting source.rule source.measurable_rule,
    delayed_terminalOnly input C accounting source.rule,
    shadowHistory accounting source.rule, measurable_shadowHistory accounting source.rule source.measurable_rule,
    ?_, ?_, ?_, ?_⟩
  · exact shadow_run input C hretained mode accounting source.rule source.legal
  · exact success_preserved input C hretained mode accounting source.rule source.legal
  · intro sample
    exact ⟨observationBill_domination input C hretained mode accounting source.rule source.legal sample,
      actualBill_domination input C hretained mode accounting source.rule source.legal sample⟩
  · intro ν _
    unfold risk
    apply measure_mono
    intro sample hfailure hsource
    exact hfailure (success_preserved input C hretained mode accounting source.rule source.legal sample hsource).1

end PaperProofs.Retained.PRetNativeRearrangement038
