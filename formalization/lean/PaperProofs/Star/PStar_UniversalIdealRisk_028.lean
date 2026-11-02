module

public import PaperProofs.Star.PStar_TwoErrorProbability_027
public import PaperProofs.Star.PStar_CurrentFailure_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarUniversalIdealRisk028

open Common Common.Native Parameters MeasureTheory PStarCurrentFailure020 PStarActualHalt022
  PStarUniversalTestErrors026 PStarTwoErrorProbability027

/-- EXACT original C07 ideal risk field for the unchanged current script,
including contracts that permit deferred physical execution. -/
theorem universalFirstIdealRisk (P : PaperProofs.Star.Parameters)
    (C : Contract (starInstance P.tools .universalFirst)) (qualified : C.IsCurrentAllocation)
    (accounting : NormalAccounting (starInstance P.tools .universalFirst)) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1/4) :
    risk (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none (Seed := Unit)) (Measure.dirac ()) ≤ ENNReal.ofReal r := by
  classical
  have domination : {sample : Unit × (P.input .universalFirst).World |
      ¬runSuccess (P.input .universalFirst) C .uncapped accounting
        (P.starReferenceRule .universalFirst .current r none) sample}
      ≤ᵐ[(P.input .universalFirst).seededWorldLaw (Measure.dirac ())]
      {sample : Unit × (P.input .universalFirst).World | sample.2 ∈
        twoErrorEvent P .universalFirst (universalStage P.tools .universalFirst)
          (singletonStage P.tools .universalFirst P.firstTool) (starTargetReal r 1) (min (1/4) (r / starTargetReal r 1))} := by
    filter_upwards [original_halts_ae P .universalFirst .current r positive quarter C qualified accounting]
      with sample eventuallyHalted
    intro failure
    rcases sample with ⟨⟨⟩, world⟩
    obtain ⟨n, halted⟩ := eventuallyHalted
    obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input .universalFirst) C .uncapped accounting
      (P.starReferenceRule .universalFirst .current r none)
      (reference_legal P .universalFirst .current r C qualified accounting) ((),world) n
    have failed : ¬(run (P.input .universalFirst) C .uncapped accounting
        (P.starReferenceRule .universalFirst .current r none) ((),world) n).ledger.success C := by
      intro success
      exact failure ⟨n, halted, success⟩
    have wrong := universalFirst_halted_failure_two_errors P r C qualified.1 accounting () _ _ path halted failed
    exact universal_two_errors_testErrors P r C qualified.1 accounting world path wrong.1 wrong.2
  exact (measure_mono_ae domination).trans (universalErrorEvent_seeded_le P r positive)

end PaperProofs.Star.PStarUniversalIdealRisk028
