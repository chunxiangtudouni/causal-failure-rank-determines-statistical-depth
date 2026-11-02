module

public import PaperProofs.Retained.PRet_JointCharges_075
public import PaperProofs.Common.NativeBellmanPrivateSeeds

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshSeedPullback094

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetJointCharges075
open BellmanPrivateSeeds
open scoped ENNReal

variable {Physical Ambient : Instance} {Large Small : Type*} [MeasurableSpace Large] [MeasurableSpace Small]

/-- Tautological ALL-tools wrapper of every full Policy, solely to reuse
mature seed-pullback implementation. No tool is removed and no available-tool
value/comparator is introduced or substituted for freshPenalty. -/
def allTools (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small) :
    AvailablePolicy input (freshContract Physical) (zeroNormalAccounting Physical) Finset.univ Small := by
  refine ⟨source, ?_⟩
  intro seed truth tapes n s hp ha handle tool heq
  exact Finset.mem_univ tool

def pullbackFull (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small)
    (f : Large → Small) (hf : Measurable f) :
    Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Large :=
  (pullbackAvailable input (freshContract Physical) (zeroNormalAccounting Physical) Finset.univ (allTools input source) f hf).val

theorem run_pullbackFull (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) (n : ℕ) :
    run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) (pullbackFull input source f hf).rule sample n =
      run input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule (f sample.1, sample.2) n :=
  run_pullbackAvailable input (freshContract Physical) (zeroNormalAccounting Physical) Finset.univ (allTools input source) f hf sample n

theorem jointSuccess_pullbackFull (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (f : Large → Small) (hf : Measurable f) (sample : Large × input.World) :
    jointSuccess input embed old (pullbackFull input source f hf).rule sample ↔
      jointSuccess input embed old source.rule (f sample.1, sample.2) := by
  simp only [jointSuccess, run_pullbackFull]

theorem expectedObservationBill_pullbackFull (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small)
    (f : Large → Small) (hf : Measurable f) (ν : Measure Large) :
    expectedObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) (pullbackFull input source f hf).rule ν =
      expectedObservationBill input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) source.rule (ν.map f) :=
  expectedObservationBill_pullbackAvailable input (freshContract Physical) (zeroNormalAccounting Physical) Finset.univ (allTools input source) f hf ν

theorem jointObjective_pullbackFull (input : StatisticalInput Physical)
    (source : Policy input (freshContract Physical) .uncapped (zeroNormalAccounting Physical) Small)
    (embed : Physical.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (f : Large → Small) (hf : Measurable f) (ν : Measure Large) (penalty : ℝ≥0∞) :
    jointObjective input embed old (pullbackFull input source f hf).rule ν penalty =
      jointObjective input embed old source.rule (ν.map f) penalty := by
  unfold jointObjective
  rw [expectedObservationBill_pullbackFull input source f hf ν]
  congr 1
  congr 1
  symm
  have hs : MeasurableSet {sample | ¬ jointSuccess input embed old source.rule sample} :=
    (measurableSet_jointSuccess input embed old source.rule source.measurable_rule).compl
  have hm : Measurable (fun sample : Large × input.World => (f sample.1, sample.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [seededWorldLaw_map_seed input ν f hf, Measure.map_apply hm hs]
  congr 1
  ext sample
  exact (not_congr (jointSuccess_pullbackFull input source embed old f hf sample)).symm

end PaperProofs.Retained.PRetFreshSeedPullback094
