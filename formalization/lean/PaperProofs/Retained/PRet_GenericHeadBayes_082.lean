module

public import PaperProofs.Common.NativeHeadBayes

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetGenericHeadBayes082

open Common Common.Native MeasureTheory
open scoped ENNReal

variable {I : Instance} {Seed : Type} [MeasurableSpace Seed]

/-- Generic shifted local lower comparison, reusing the ORIGINAL local
infimum and actual native head-exit test. Continuation prices are genuine
scalar parameters, so retained old-H successors can be substituted without
identifying them with the current available-tool G value. -/
theorem shifted_localValue_lower (input : StatisticalInput I) (head : I.Stage)
    (source : PolicyRule I Seed) (hm : MeasurableRule source)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (good bad : ℝ) (hgood : 0 ≤ good) (horder : good ≤ bad) :
    ENNReal.ofReal (good + (input.experiment head).localValueReal (bad - good)) ≤
      ∫⁻ sample, (input.experiment head).observationCharge
        ((nativeHeadTest input head source hm).rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if (nativeHeadTest input head source hm).rule.decision sample.1 (worldTapes input sample.2 head) =
          input.truthAt sample.2 head then ENNReal.ofReal good else ENNReal.ofReal bad) ∂input.seededWorldLaw ν := by
  let E := input.experiment head
  have hj : ENNReal.ofReal (E.localValueReal (bad - good)) = E.localValue (ENNReal.ofReal (bad - good)) :=
    ENNReal.ofReal_toReal (E.localValue_ofReal_ne_top (bad - good))
  calc
    _ = ENNReal.ofReal good + E.localValue (ENNReal.ofReal (bad - good)) := by
      rw [ENNReal.ofReal_add hgood (E.localValueReal_nonneg (bad - good)), hj]
    _ ≤ ENNReal.ofReal good + E.bayesObjective ν (nativeHeadTest input head source hm) (ENNReal.ofReal (bad - good)) :=
      add_le_add le_rfl (E.localValue_le_test ν (nativeHeadTest input head source hm) _)
    _ = _ := shiftedBayesObjective_eq_seededWorld_integral input head ν (nativeHeadTest input head source hm) good bad hgood horder

end PaperProofs.Retained.PRetGenericHeadBayes082
