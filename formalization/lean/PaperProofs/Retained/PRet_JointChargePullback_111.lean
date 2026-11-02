module

public import PaperProofs.Retained.PRet_FreshSeedPullback_094

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetJointChargePullback111

open Common Common.Native PRetAmbientComparator073 PRetJointCharges075 PRetFreshSeedPullback094

variable {I Ambient : Instance} {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]

theorem runObservationBill_pullbackFull (input : StatisticalInput I)
    (source : Policy input (freshContract I) .uncapped (zeroNormalAccounting I) Small)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) :
    runObservationBill input (freshContract I) .uncapped (zeroNormalAccounting I) (pullbackFull input source f hf).rule sample =
      runObservationBill input (freshContract I) .uncapped (zeroNormalAccounting I) source.rule (f sample.1, sample.2) := by
  unfold runObservationBill
  apply iSup_congr
  intro n
  rw [run_pullbackFull]

theorem jointCharge_pullbackFull (input : StatisticalInput I)
    (source : Policy input (freshContract I) .uncapped (zeroNormalAccounting I) Small)
    (embed : I.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) (penalty : ENNReal) :
    jointCharge input embed old (pullbackFull input source f hf).rule penalty sample =
      jointCharge input embed old source.rule penalty (f sample.1, sample.2) := by
  unfold jointCharge
  rw [runObservationBill_pullbackFull, jointSuccess_pullbackFull]

end PaperProofs.Retained.PRetJointChargePullback111
