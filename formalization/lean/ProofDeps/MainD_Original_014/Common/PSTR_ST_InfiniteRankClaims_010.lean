module

public import Common.PSTR_ST_TableInfinite_009
public import PaperProofs.Common.ReferenceObservationCost
public import PaperProofs.Common.NativeCostBound

/-! Full original L01 InfiniteRankClaims for the actual table tie. Original
THIS-script complete-H0 and numeric caps are used only for native transfer.
All-sample success and zero observations are proved before that transfer. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableInfinite

open PaperProofs.Structure PaperProofs.Structure.LaminarTree CompactPrice

variable {I : Instance}

theorem tableExpectedObservationBill_infiniteRank (input : StatisticalInput I)
    (hlaminar : LaminarSchedule I.compatibility) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (ν : Measure Unit) :
    expectedObservationBill input C .uncapped accounting (tableRule input available budget limit) ν = 0 := by
  have hlegal := tableRule_uncapped_legal input C hearly accounting available budget limit
  have hzero (stage : I.Stage) (sample : Unit × input.World) :
      runStageObservationBill input C .uncapped accounting (tableRule input available budget limit) stage sample = 0 := by
    unfold runStageObservationBill
    apply le_antisymm (iSup_le fun n => ?_) bot_le
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (tableRule input available budget limit) hlegal sample n
    have hz := prefix_table_reviews_zero_of_infinite_rank hlaminar input C hearly accounting
      available budget hbudget hsmall htop limit sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage
    simp [hz]
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal
    (tableUncappedPolicy input C hearly accounting available budget limit).measurable_rule]
  simp only [hzero, lintegral_zero, Finset.sum_const_zero]

theorem infiniteRankClaims : CompactPrice.InfiniteRankClaims := by
  intro I hlaminar input available htop C hcurrent accounting budget exponent hbudget hsmall qualification
  obtain ⟨policy, hrule, hrun, _caps⟩ := tableNativeImplementation input C hcurrent.1 accounting
    available budget exponent qualification
  have hzeroObservation : expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 := by
    calc
      _ = expectedObservationBill input C .uncapped accounting
          (tableRule input available budget (some (referenceQuota input exponent))) (Measure.dirac ()) := by
        unfold expectedObservationBill runObservationBill
        simp_rw [hrun]
      _ = 0 := tableExpectedObservationBill_infiniteRank input hlaminar C hcurrent.1 accounting available budget
        hbudget hsmall htop (some (referenceQuota input exponent)) (Measure.dirac ())
  refine ⟨policy, hrule, ?_, hzeroObservation, ?_⟩
  · calc
      _ = risk input C .uncapped accounting
          (tableRule input available budget (some (referenceQuota input exponent))) (Measure.dirac ()) := by
        unfold risk runSuccess
        simp_rw [hrun]
      _ = 0 := tableRisk_zero_of_infinite_rank hlaminar input C hcurrent.1 accounting available budget
        hbudget hsmall htop (some (referenceQuota input exponent)) (Measure.dirac ())
  · have hb := expectedBill_le_observation_add input C .native accounting policy (Measure.dirac ())
    rw [hzeroObservation, zero_add] at hb
    exact hb

end PaperProofs.Common.Native.PSTRStatistics.TableInfinite
