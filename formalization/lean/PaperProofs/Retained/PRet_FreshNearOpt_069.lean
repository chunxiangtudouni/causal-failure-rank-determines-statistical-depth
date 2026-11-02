module

public import PaperProofs.Retained.PRet_FreshLocalPrices_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshNearOpt069

open Common Common.Native MeasureTheory

open scoped ENNReal

variable {I : Instance}

/-- Near-optimal TRUE full fresh continuations are selected from the
independently defined infimum. Optimal attainment is not assumed. -/
theorem exists_freshObjective_near (input : StatisticalInput I) (first : ℕ) (old : Finset I.Stage)
    (penalty : ℝ≥0∞) (hpenalty : penalty ≠ ⊤) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (SmallSeed : Type) (m : MeasurableSpace SmallSeed),
      let : MeasurableSpace SmallSeed := m
      ∃ (ν : Measure SmallSeed) (_hν : IsProbabilityMeasure ν)
        (policy : Policy (input.freshSuffix first) (freshContract (I.freshSuffix first)) .uncapped
          (zeroNormalAccounting (I.freshSuffix first)) SmallSeed),
        freshObjective input first old policy.rule ν penalty < freshPenalty input first old penalty + ENNReal.ofReal epsilon := by
  have hfinite := freshPenalty_ne_top input first old hpenalty
  have hpositive : ENNReal.ofReal epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr hepsilon).ne'
  have hnear := ENNReal.lt_add_right hfinite hpositive
  conv_lhs at hnear => unfold freshPenalty
  simpa only [iInf_lt_iff] using hnear

end PaperProofs.Retained.PRetFreshNearOpt069


