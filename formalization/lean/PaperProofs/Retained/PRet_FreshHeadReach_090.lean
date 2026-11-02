module

public import PaperProofs.Retained.PRet_FreshHeadEntry_087
public import PaperProofs.Retained.PRet_GenericHeadWeights_089
public import PaperProofs.Common.EntryContinuationPartition

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadReach090

open Common Common.Native MeasureTheory PRetFreshHeadEntry087 PRetGenericHeadWeights089 PRetJointExtraction076
open EntryContinuationPartition
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- All genuine next-stage arrivals are partitioned by their unique actual
record. Every correct/error old-H branch pays the original continuation value,
without conditioning the private seed or selecting an optimal continuation. -/
theorem head_reach_continuation_lower (input : StatisticalInput I) (original : I.Stage) (old : Finset I.Stage)
    (source : Policy (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix original.val)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : (I.freshSuffix original.val).Stage) (hnext : next.val = 1)
    (penalty : ℝ) (hp : 0 ≤ penalty) :
    (∫⁻ sample in reachGate (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix original.val)) source.rule next Set.univ,
      decisionWeight (input.freshSuffix original.val) (I.freshHead original) source.rule
        (goodPenaltyReal input original old penalty) (badPenaltyReal input original old penalty) sample
          ∂(input.freshSuffix original.val).seededWorldLaw ν) ≤
    ∫⁻ sample in reachGate (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix original.val)) source.rule next Set.univ,
      futureJointCharge (input.freshSuffix original.val) (I.freshStageLift original.val) old source.rule 1 (ENNReal.ofReal penalty) sample
        ∂(input.freshSuffix original.val).seededWorldLaw ν := by
  classical
  let J := I.freshSuffix original.val
  let localInput := input.freshSuffix original.val
  let head := I.freshHead original
  let good := goodPenaltyReal input original old penalty
  let bad := badPenaltyReal input original old penalty
  let μ := localInput.seededWorldLaw ν
  let weight := decisionWeight localInput head source.rule good bad
  let charge := futureJointCharge localInput (I.freshStageLift original.val) old source.rule 1 (ENNReal.ofReal penalty)
  let E := indexedEvent localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule next Set.univ
  have hmE (record : Record J) : MeasurableSet (E record) :=
    measurableSet_recordEvent localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.measurable_rule next record.1 record.2 Set.univ MeasurableSet.univ
  have hon (record : Record J) (sample : Seed × localInput.World) (hs : sample ∈ E record) :
      weight sample = entryWeight head record.2 good bad := by
    obtain ⟨hentry, hstartup⟩ := recordEvent_firstEntry localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule next record.1 record.2 Set.univ sample hs
    have he : FirstEntryAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule 1 record.1 sample :=
      hnext ▸ hentry
    have hw := decisionWeight_on_entry localInput (freshContract J) rfl (zeroNormalAccounting J) source.rule
      source.legal head rfl sample record.1 he good bad
    rw [hstartup] at hw
    exact hw
  have hrow (record : Record J) : (∫⁻ sample in E record, weight sample ∂μ) ≤ ∫⁻ sample in E record, charge sample ∂μ := by
    have hb := head_entry_lower input original old source ν next hnext record.1 record.2 penalty hp
    have heq : entryWeight head record.2 good bad =
        ENNReal.ofReal (if HeadCorrectStartup head record.2 then good else bad) := by
      unfold entryWeight
      split_ifs <;> rfl
    calc
      _ = ∫⁻ _sample in E record, entryWeight head record.2 good bad ∂μ :=
        setLIntegral_congr_fun (hmE record) (hon record)
      _ = entryWeight head record.2 good bad * μ (E record) := setLIntegral_const _ _
      _ ≤ ∫⁻ sample in E record, charge sample ∂μ := by
        rw [heq]
        simpa only [E, indexedEvent, recordEvent, Set.mem_univ, true_and] using hb
  rw [lintegral_eq_tsum_entry_records localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.measurable_rule next Set.univ MeasurableSet.univ μ weight,
    lintegral_eq_tsum_entry_records localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.measurable_rule next Set.univ MeasurableSet.univ μ charge]
  exact ENNReal.tsum_le_tsum hrow

end PaperProofs.Retained.PRetFreshHeadReach090
