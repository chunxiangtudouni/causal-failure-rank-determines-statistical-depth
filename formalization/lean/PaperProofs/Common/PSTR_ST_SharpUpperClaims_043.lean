module

public import PaperProofs.Common.PSTR_ST_SelectorSharpCost_042
public import PaperProofs.Common.PSTR_ST_TableNativeRisk_017
public import PaperProofs.Common.ReferenceSharpNativeUpper

/-! The unchanged original TABLE SharpUpperClaims. Fixed input precedes
cutoff; every selector specification, actual fee recurrence, shorter-child
cost hypothesis, original risk and native-cap obligation is discharged. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics

open PaperProofs.Statistics PaperProofs.Structure

theorem sharpUpperClaims : CompactPrice.SharpUpperClaims := by
  intro I hlaminar input available depth hrank epsilon hepsilon
  have hfinite : errorRank I.compatibility available ≠ ⊤ := by
    rw [hrank]
    exact ENat.natCast_ne_top depth
  have hcoefficient := input.orderedCoefficient_pos available hfinite
  have hdepth : 1 ≤ depth := by
    have hp := errorRank_pos I.compatibility available
    rw [hrank] at hp
    have : 0 < depth := by exact_mod_cast hp
    omega
  let eta := min (epsilon / 4) 1
  have heta : 0 < eta := lt_min (by positivity) (by norm_num)
  have hetaOne : eta ≤ 1 := min_le_right _ _
  have hetaEpsilon : eta ≤ epsilon / 4 := min_le_left _ _
  have hproduct : (1 + eta) * (1 + eta) ≤ 1 + epsilon := by
    have hsquare : eta * eta ≤ eta := by nlinarith
    nlinarith
  obtain ⟨costCutoff, hcostCutoff, hcost⟩ :=
    MaxSelector.Asymptotics.tableIdealCostAsymptotics input hlaminar available depth hrank eta heta
  obtain ⟨logCutoff, hlogCutoff, hlogs⟩ :=
    iteratedLog_factorTwo_uniform_cutoff depth hdepth eta heta
  refine ⟨min costCutoff logCutoff, lt_min hcostCutoff hlogCutoff, ?_⟩
  intro delta hdelta hcut hsmall budget exponent choice C hcurrent accounting qualification
  have hbudgetCut : (budget : ℝ) < costCutoff :=
    choice.conservative.trans_lt (hcut.trans_le (min_le_left _ _))
  have hlog := hlogs delta (budget : ℝ) hdelta (hcut.trans_le (min_le_right _ _))
    choice.factor_two choice.conservative
  have hcostBound := hcost budget choice.positive choice.small hbudgetCut C hcurrent accounting
  obtain ⟨policy, hrule, _hrun, _hcaps, hrisk, hbill⟩ :=
    TableNativeRisk.tableNativeStatisticalClaims input hlaminar C hcurrent accounting available delta
      hdelta hsmall budget exponent choice qualification
  refine ⟨policy, hrule, hrisk, ?_⟩
  rw [PaperProofs.Common.SymbolicPrice.inputExpression_eval]
  calc
    _ ≤ expectedBill input C .uncapped accounting
        (CompactPrice.tableRule input available budget none) (Measure.dirac ()) := hbill
    _ ≤ ENNReal.ofReal ((1 + eta) * input.orderedCoefficient available *
        iteratedLog depth (budget : ℝ)⁻¹) := hcostBound
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ (1 + eta) * input.orderedCoefficient available *
            ((1 + eta) * iteratedLog depth (1 / delta)) :=
          mul_le_mul_of_nonneg_left (by simpa only [one_div] using hlog.2) (by positivity)
        _ = ((1 + eta) * (1 + eta)) * input.orderedCoefficient available *
            iteratedLog depth (1 / delta) := by ring
        _ ≤ _ := by
          simpa only [one_div] using mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hproduct hcoefficient.le) hlog.1.le)

end PaperProofs.Common.Native.PSTRStatistics
