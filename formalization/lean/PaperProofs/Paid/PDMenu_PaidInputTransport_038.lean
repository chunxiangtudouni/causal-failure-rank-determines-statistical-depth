module

public import PaperProofs.Paid.PDMenu_FreshSuffixPaid_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Only a genuine dependent equality of original instance and input data is
transported; the underlying native rule, rights and accounting stay exact. -/
def transportPaidPolicy {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy left (paidRelaxedContract J) .uncapped (zeroNormalAccounting J) Seed) :
    Policy right (paidRelaxedContract K) .uncapped (zeroNormalAccounting K) Seed := by
  cases hI
  cases eq_of_heq hinput
  exact source

theorem paidPenaltyObjective_transportPaidPolicy {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : Policy left (paidRelaxedContract J) .uncapped (zeroNormalAccounting J) Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective right (paidRelaxedContract K) (zeroNormalAccounting K)
      (transportPaidPolicy hI left right hinput source).rule ν penalty =
      paidPenaltyObjective left (paidRelaxedContract J) (zeroNormalAccounting J) source.rule ν penalty := by
  cases hI
  cases eq_of_heq hinput
  rfl

def transportPaidAvailable {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    (leftAvailable : Finset J.Tool) (rightAvailable : Finset K.Tool) (hAvailable : HEq leftAvailable rightAvailable)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : AvailablePolicy left (paidRelaxedContract J) (zeroNormalAccounting J) leftAvailable Seed) :
    AvailablePolicy right (paidRelaxedContract K) (zeroNormalAccounting K) rightAvailable Seed := by
  cases hI
  cases eq_of_heq hinput
  cases eq_of_heq hAvailable
  exact source

theorem paidPenaltyObjective_transportPaidAvailable {J K : Instance} (hI : J = K)
    (left : StatisticalInput J) (right : StatisticalInput K) (hinput : HEq left right)
    (leftAvailable : Finset J.Tool) (rightAvailable : Finset K.Tool) (hAvailable : HEq leftAvailable rightAvailable)
    {Seed : Type*} [MeasurableSpace Seed]
    (source : AvailablePolicy left (paidRelaxedContract J) (zeroNormalAccounting J) leftAvailable Seed)
    (ν : Measure Seed) (penalty : ℝ≥0∞) :
    paidPenaltyObjective right (paidRelaxedContract K) (zeroNormalAccounting K)
      (transportPaidAvailable hI left right hinput leftAvailable rightAvailable hAvailable source).val.rule ν penalty =
      paidPenaltyObjective left (paidRelaxedContract J) (zeroNormalAccounting J) source.val.rule ν penalty := by
  cases hI
  cases eq_of_heq hinput
  cases eq_of_heq hAvailable
  rfl

end PDMenu

