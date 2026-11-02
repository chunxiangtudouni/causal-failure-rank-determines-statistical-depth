module

public import PaperProofs.Common.PSTR_ST_TableTruncation_016
public import PaperProofs.Common.PSTR_ST_TableMass_013

/-! The original table controller's native statistical/resource conclusions.
Actual original H0/quota qualifications are preserved; the physical hybrid
cost field of NativeControllerClaims remains a separate original obligation. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableNativeRisk

open PaperProofs.Structure.LaminarTree
open CompactPrice TableAlignment TableDecision TableOverflow TableMass TableTruncation

variable {I : Instance}

theorem tableBounded_risk (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (budget : ℚ) (exponent : ℕ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    risk input C .uncapped accounting (tableRule input available budget (some (referenceQuota input exponent)))
      (Measure.dirac ()) ≤ ENNReal.ofReal delta := by
  have hi := tableIdealRisk_le_half hlaminar input C hearly accounting available budget choice.positive choice.small
  have ht := tableRisk_le_ideal_add_overflow input C hearly accounting available budget (referenceQuota input exponent)
  have ho := tableOverflowGuarantee input hlaminar C hearly accounting available delta hsmall exponent budget choice
  have half : ENNReal.ofReal ((budget : ℝ) / 2) ≤ ENNReal.ofReal (delta / 2) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right choice.conservative (by norm_num))
  calc
    _ ≤ ENNReal.ofReal (delta / 2) + ENNReal.ofReal (delta / 2) :=
      ht.trans (add_le_add (hi.trans half) ho)
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ delta / 2) (by positivity : 0 ≤ delta / 2)]
      congr 1
      ring

theorem tableNativeStatisticalClaims (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2) (budget : ℚ) (exponent : ℕ)
    (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : OriginalQualification input C accounting available budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = tableRule input available budget (some (referenceQuota input exponent)) ∧
      (∀ sample clock, run input C .native accounting policy.rule sample clock =
        run input C .uncapped accounting (tableRule input available budget (some (referenceQuota input exponent))) sample clock) ∧
      (∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C ∧
        (run input C .native accounting policy.rule sample clock).ledger.normalCalls ≤ (C.normalCallBound : ℕ∞)) ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting (tableRule input available budget none) (Measure.dirac ()) := by
  obtain ⟨policy, hrule, hrun, hcaps⟩ := tableNativeImplementation input C hcurrent.1 accounting available budget exponent qualification
  refine ⟨policy, hrule, hrun, hcaps, ?_, ?_⟩
  · calc
      _ = risk input C .uncapped accounting
          (tableRule input available budget (some (referenceQuota input exponent))) (Measure.dirac ()) := by
        unfold risk runSuccess
        simp_rw [hrun]
      _ ≤ _ := tableBounded_risk input hlaminar C hcurrent.1 accounting available delta hd hsmall budget exponent choice
  · calc
      _ = expectedBill input C .uncapped accounting
          (tableRule input available budget (some (referenceQuota input exponent))) (Measure.dirac ()) := by
        unfold expectedBill runActualBill
        simp_rw [hrun]
      _ ≤ _ := lintegral_mono (tableRunActualBill_le_ideal input C hcurrent.1 accounting available budget (referenceQuota input exponent))

end PaperProofs.Common.Native.PSTRStatistics.TableNativeRisk
