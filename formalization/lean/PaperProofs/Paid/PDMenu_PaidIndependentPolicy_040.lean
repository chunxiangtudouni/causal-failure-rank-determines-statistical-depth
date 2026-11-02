module

public import PaperProofs.Paid.PDMenu_CurrentHeadKernel_006
public import PaperProofs.Common.NativeBellmanPrivateSeeds

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open BellmanPrivateSeeds

variable {I : Instance}

noncomputable def paidIndependentPolicy {Local Good Bad : Type*}
    [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]
    (input : StatisticalInput I) (head : I.Stage) (available : Finset I.Tool) (repair : Option I.Tool)
    (test : (input.experiment head).AdmissibleRule Local)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (badAvailable : Finset I.Tool)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable Bad) :
    AvailablePolicy input (paidRelaxedContract I) (zeroNormalAccounting I) available
      (CombinedSeed Local Good Bad) := by
  let test' : (input.experiment head).AdmissibleRule (CombinedSeed Local Good Bad) :=
    pullbackTest (input.experiment head) test localSeed measurable_localSeed
  let good' : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available (CombinedSeed Local Good Bad) :=
    pullbackAvailable (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
    (zeroNormalAccounting (I.freshSuffix 1)) available good goodSeed measurable_goodSeed
  let bad' : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable (CombinedSeed Local Good Bad) :=
    pullbackAvailable (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
    (zeroNormalAccounting (I.freshSuffix 1)) badAvailable bad badSeed measurable_badSeed
  exact paidHeadThenPolicy input (paidRelaxedContract I) (paidRelaxedContract_rights I) (zeroNormalAccounting I)
    head test' available (bellmanPostHeadRaw input head repair good'.val.rule bad'.val.rule)
    (measurable_bellmanPostHeadRaw input head repair good'.val.rule bad'.val.rule
      good'.val.measurable_rule bad'.val.measurable_rule)


end PDMenu
