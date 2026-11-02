module

public import RootB23_PrepScalarMinimality_001
public import PaperProofs.Common.RationalControllerComputation

/-! Typed ORIGINAL-input consumers. No H0, numericQualification, supplied
quota, width, output oracle, or additional input restriction is assumed.
These only bound the scalar scan counts; all actual native runs remain
the separate execution-line obligation. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation

namespace RootB23.PrepScalar

theorem original_stage_counters_bounded (I : Instance) (input : StatisticalInput I)
    (C : Contract I) (budget : Rat) (stage : I.Stage) :
    computedExponent (I:=I) budget ≤ arithmeticScale input C budget ∧
      (input.experiment stage).priorIntegerMax ≤ arithmeticScale input C budget ∧
      (input.experiment stage).channelIntegerMax ≤ arithmeticScale input C budget ∧
      computedQuotas input budget stage ≤ arithmeticScale input C budget := by
  have eq_sum : computedQuotas input budget stage ≤ numericalQuota input budget :=
    Finset.single_le_sum (fun other _ => Nat.zero_le (computedQuotas input budget other))
      (Finset.mem_univ stage)
  have sum_le : numericalQuota input budget ≤ arithmeticScale input C budget := by
    unfold arithmeticScale
    omega
  have Q_le := eq_sum.trans sum_le
  have exponent_prior := exponent_add_prior_le_quota (input.experiment stage) (computedExponent (I:=I) budget)
  have pair : computedExponent (I:=I) budget+(input.experiment stage).priorIntegerMax ≤
      computedQuotas input budget stage := by
    simpa only [computedQuotas,referenceQuota] using exponent_prior
  have positive : 1 ≤ computedExponent (I:=I) budget := by
    unfold computedExponent BinaryExperiment.quotaExponent
    exact le_max_left _ _
  have channel := channel_integer_le_quota (input.experiment stage) (computedExponent (I:=I) budget) positive
  have M_le : (input.experiment stage).channelIntegerMax ≤ computedQuotas input budget stage := by
    simpa only [computedQuotas,referenceQuota] using channel
  exact ⟨(Nat.le_add_right _ _).trans (pair.trans Q_le),
    (Nat.le_add_left _ _).trans (pair.trans Q_le),M_le.trans Q_le,Q_le⟩

theorem original_channel_ratio_scan_bounded (I : Instance) (input : StatisticalInput I)
    (C : Contract I) (budget : Rat) (stage : I.Stage)
    (symbol : Fin (input.experiment stage).alphabetSize) :
    BinaryExperiment.ratioIntegerBound
      ((input.experiment stage).channel true symbol/(input.experiment stage).channel false symbol) ≤
        arithmeticScale input C budget := by
  have local_bound : BinaryExperiment.ratioIntegerBound
      ((input.experiment stage).channel true symbol/(input.experiment stage).channel false symbol) ≤
        (input.experiment stage).channelIntegerMax :=
    Finset.le_sup (f:=fun y => BinaryExperiment.ratioIntegerBound
      ((input.experiment stage).channel true y/(input.experiment stage).channel false y))
      (Finset.mem_univ symbol)
  exact local_bound.trans (original_stage_counters_bounded I input C budget stage).2.2.1

theorem original_global_exponent_bounded (I : Instance) (input : StatisticalInput I)
    (C : Contract I) (budget : Rat) :
    computedExponent (I:=I) budget ≤ arithmeticScale input C budget := by
  by_cases empty : I.stageCount=0
  · have one : computedExponent (I:=I) budget=1 := by
      simpa only [computedExponent,empty] using exponent_zero_stages budget
    rw [one]
    unfold arithmeticScale
    omega
  · let stage : I.Stage := ⟨0,Nat.pos_of_ne_zero empty⟩
    exact (original_stage_counters_bounded I input C budget stage).1

end RootB23.PrepScalar
