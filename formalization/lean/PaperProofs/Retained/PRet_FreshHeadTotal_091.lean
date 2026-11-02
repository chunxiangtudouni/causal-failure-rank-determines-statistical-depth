module

public import PaperProofs.Retained.PRet_FreshHeadReach_090
public import PaperProofs.Retained.PRet_FreshNoEntry_085
public import PaperProofs.Retained.PRet_FutureBillDecomposition_086
public import PaperProofs.Retained.PRet_FreshLocalPrices_042

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshHeadTotal091

open Common Common.Native MeasureTheory PRetFreshHeadReach090 PRetFreshNoEntry085
open PRetFutureBillDecomposition086 PRetFreshLocalPrices042 PRetGenericHeadWeights089
open PRetAmbientComparator073 PRetJointCharges075 PRetJointExtraction076 EntryContinuationPartition
open scoped ENNReal

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- The complete arbitrary fresh-Policy head lower bound. True arrivals
pay actual old-H continuations; the no-arrival complement pays its original
single failure penalty. Every bought observation stays in the actual bill. -/
theorem integrated_head_lower (input : StatisticalInput I) (original : I.Stage) (old : Finset I.Stage)
    (source : Policy (input.freshSuffix original.val) (freshContract (I.freshSuffix original.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix original.val)) Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (next : (I.freshSuffix original.val).Stage) (hnext : next.val = 1)
    (penalty : ℝ) (hp : 0 ≤ penalty) :
    (∫⁻ sample, ((input.freshSuffix original.val).experiment (I.freshHead original)).observationCharge
        (headExitStop (input.freshSuffix original.val) (I.freshHead original) source.rule sample.1
          (worldTapes (input.freshSuffix original.val) sample.2 (I.freshHead original))) +
      decisionWeight (input.freshSuffix original.val) (I.freshHead original) source.rule
        (goodPenaltyReal input original old penalty) (badPenaltyReal input original old penalty) sample
          ∂(input.freshSuffix original.val).seededWorldLaw ν) ≤
      jointObjective (input.freshSuffix original.val) (I.freshStageLift original.val) old source.rule ν (ENNReal.ofReal penalty) := by
  let J := I.freshSuffix original.val
  let localInput := input.freshSuffix original.val
  let head := I.freshHead original
  let μ := localInput.seededWorldLaw ν
  let reach := reachGate localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule next Set.univ
  let localCharge := fun sample : Seed × localInput.World => (localInput.experiment head).observationCharge
    (headExitStop localInput head source.rule sample.1 (worldTapes localInput sample.2 head))
  let weight := decisionWeight localInput head source.rule (goodPenaltyReal input original old penalty) (badPenaltyReal input original old penalty)
  let future := futureJointCharge localInput (I.freshStageLift original.val) old source.rule 1 (ENNReal.ofReal penalty)
  let total := jointCharge localInput (I.freshStageLift original.val) old source.rule (ENNReal.ofReal penalty)
  have hmReach : MeasurableSet reach := measurableSet_reachGate localInput (freshContract J) .uncapped
    (zeroNormalAccounting J) source.rule source.measurable_rule next Set.univ MeasurableSet.univ
  have hmLocal : Measurable localCharge := measurable_nativeHeadLocalCharge localInput head source.rule source.measurable_rule
  have hArrival := head_reach_continuation_lower input original old source ν next hnext penalty hp
  have hdecomp (sample : Seed × localInput.World) (hs : sample ∈ reach) : total sample = localCharge sample + future sample := by
    change sample ∈ reachGate localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule next Set.univ at hs
    rw [← iUnion_indexedEvent_eq_reachGate localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule next Set.univ] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    obtain ⟨hentry, _⟩ := recordEvent_firstEntry localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule next record.1 record.2 Set.univ sample hr
    have he : FirstEntryAt localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule 1 record.1 sample := hnext ▸ hentry
    dsimp only [total, future, jointCharge, futureJointCharge, localCharge]
    rw [runObservationBill_eq_entry_add_futureFilter localInput (freshContract J) .uncapped (zeroNormalAccounting J)
      source.rule source.legal sample 1 record.1 he,
      firstEntry_one_prefix_observationBill localInput (freshContract J) (zeroNormalAccounting J) source.rule source.legal head rfl sample record.1 he]
    exact add_assoc _ _ _
  have hreach : (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) ≤ ∫⁻ sample in reach, total sample ∂μ := by
    rw [lintegral_add_left hmLocal]
    calc
      _ ≤ (∫⁻ sample in reach, localCharge sample ∂μ) + ∫⁻ sample in reach, future sample ∂μ := add_le_add le_rfl hArrival
      _ = ∫⁻ sample in reach, localCharge sample + future sample ∂μ := (lintegral_add_left hmLocal _).symm
      _ = _ := setLIntegral_congr_fun hmReach (fun sample hs => (hdecomp sample hs).symm)
  have hnoReach : (∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ) ≤ ∫⁻ sample in reachᶜ, total sample ∂μ := by
    apply setLIntegral_mono' hmReach.compl
    intro sample hs
    have hnever : ∀ n, (run localInput (freshContract J) .uncapped (zeroNormalAccounting J) source.rule sample n).cursor ≠ 1 := by
      intro n hc
      apply hs
      refine ⟨Set.mem_univ sample.1, n, ?_⟩
      rw [hnext]
      exact hc
    have hw : weight sample ≤ ENNReal.ofReal penalty := decisionWeight_le localInput head source.rule _ _ penalty
      (goodPenalty_le_badPenalty input original old penalty hp) (badPenalty_le_penalty input original old penalty hp) sample
    exact no_entry_charge_lower localInput source (I.freshStageLift original.val) old head next rfl hnext sample hnever
      (weight sample) (ENNReal.ofReal penalty) hw
  rw [jointObjective_eq_lintegral _ _ _ _ source.measurable_rule]
  change (∫⁻ sample, localCharge sample + weight sample ∂μ) ≤ ∫⁻ sample, total sample ∂μ
  calc
    _ = (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) + ∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ :=
      (lintegral_add_compl _ hmReach).symm
    _ ≤ (∫⁻ sample in reach, total sample ∂μ) + ∫⁻ sample in reachᶜ, total sample ∂μ := add_le_add hreach hnoReach
    _ = _ := lintegral_add_compl _ hmReach

end PaperProofs.Retained.PRetFreshHeadTotal091
