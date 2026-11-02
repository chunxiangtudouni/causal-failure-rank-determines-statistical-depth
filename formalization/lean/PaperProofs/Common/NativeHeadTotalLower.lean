module

public import PaperProofs.Common.NativeHeadAccounting
public import PaperProofs.Common.NativeHeadBranchPartition
public import PaperProofs.Common.NativeHeadTerminalLower

/-! Arbitrary-policy head-stage lower bound assembled over all genuine
arrival records and the original failure complement. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open EntryContinuationPartition NativeHeadBranchPartition

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_nativeHeadLocalCharge (input : StatisticalInput I) (head : I.Stage)
    (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (fun sample : Seed × input.World => (input.experiment head).observationCharge
      (headExitStop input head rule sample.1 (worldTapes input sample.2 head))) := by
  have hstage : Measurable (fun sample : Seed × input.World =>
      (sample.1, worldTapes input sample.2 head)) := measurable_fst.prodMk
    (((measurable_pi_apply head).comp measurable_snd).snd)
  exact (measurable_of_countable (input.experiment head).observationCharge).comp
    ((measurable_headExitStop input head rule hm).comp hstage)

/-- For an entirely arbitrary measurable R-legal policy, its original total
objective pays the SAME extracted local testing charge and the independently
defined Gg/Gb continuation weight. Every next-stage arrival is included once;
the no-arrival complement is paid by original global failure, without assuming
termination, MAP decisions, a chosen optimal tool, or finite expected charge. -/
theorem nativeHead_integrated_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : I.Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (price : ℝ) (hprice : 0 ≤ price) :
    (∫⁻ sample, (input.experiment head).observationCharge
        (headExitStop input head policy.val.rule sample.1 (worldTapes input sample.2 head)) +
      nativeHeadContinuationWeight input head R price policy.val.rule sample ∂input.seededWorldLaw ν) ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν (ENNReal.ofReal price) := by
  let μ := input.seededWorldLaw ν
  let reach := reachGate input C .uncapped accounting policy.val.rule next Set.univ
  let localCharge := fun sample : Seed × input.World => (input.experiment head).observationCharge
    (headExitStop input head policy.val.rule sample.1 (worldTapes input sample.2 head))
  let weight := nativeHeadContinuationWeight input head R price policy.val.rule
  let arrivalWeight := entryBranchWeight input C .uncapped accounting policy.val.rule next head R price
  let arrivalCharge := entryContinuationCharge input C .uncapped accounting policy.val.rule next (ENNReal.ofReal price)
  let totalCharge := runPenaltyCharge input C .uncapped accounting policy.val.rule (ENNReal.ofReal price)
  have hmReach : MeasurableSet reach := measurableSet_reachGate input C .uncapped accounting policy.val.rule policy.val.measurable_rule next Set.univ MeasurableSet.univ
  have hmLocal : Measurable localCharge := measurable_nativeHeadLocalCharge input head policy.val.rule policy.val.measurable_rule
  have hArrival := weighted_arrival_lower input C hC accounting R policy ν head next hhead hnext Set.univ MeasurableSet.univ price hprice
  have hweightOnReach sample (hs : sample ∈ reach) : weight sample = arrivalWeight sample := by
    change sample ∈ reachGate input C .uncapped accounting policy.val.rule next Set.univ at hs
    rw [← iUnion_indexedEvent_eq_reachGate input C .uncapped accounting policy.val.rule next Set.univ] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next record.1 record.2 Set.univ sample hr
    have he : FirstEntryAt input C .uncapped accounting policy.val.rule 1 record.1 sample := hnext ▸ hf.1
    have hw := nativeHeadContinuationWeight_on_entry input C hC.1 accounting policy.val.rule policy.val.legal head hhead sample record.1 he R price
    rw [hf.2] at hw
    have hp := pieces_on_record input C .uncapped accounting policy.val.rule next
      (fun r _ => ENNReal.ofReal (headEntryContinuationReal input head R price r.2)) Set.univ record sample hr
    exact hw.trans hp.symm
  have hchargeOnReach sample (hs : sample ∈ reach) : totalCharge sample = localCharge sample + arrivalCharge sample := by
    change sample ∈ reachGate input C .uncapped accounting policy.val.rule next Set.univ at hs
    rw [← iUnion_indexedEvent_eq_reachGate input C .uncapped accounting policy.val.rule next Set.univ] at hs
    obtain ⟨record, hr⟩ := Set.mem_iUnion.mp hs
    have hf := recordEvent_firstEntry input C .uncapped accounting policy.val.rule next record.1 record.2 Set.univ sample hr
    have he : FirstEntryAt input C .uncapped accounting policy.val.rule 1 record.1 sample := hnext ▸ hf.1
    have hd := firstEntry_one_penaltyCharge_decomposition input C accounting policy.val.rule policy.val.legal head hhead sample record.1 he (ENNReal.ofReal price)
    have hp := pieces_on_record input C .uncapped accounting policy.val.rule next
      (fun r => historyComparisonCharge input C .uncapped accounting policy.val.rule r.1 (ENNReal.ofReal price)) Set.univ record sample hr
    exact hd.trans (congrArg (localCharge sample + ·) hp.symm)
  have hreachBound : (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) ≤
      ∫⁻ sample in reach, totalCharge sample ∂μ := by
    rw [lintegral_add_left hmLocal]
    calc
      (∫⁻ sample in reach, localCharge sample ∂μ) + ∫⁻ sample in reach, weight sample ∂μ =
          (∫⁻ sample in reach, localCharge sample ∂μ) + ∫⁻ sample in reach, arrivalWeight sample ∂μ := by
        congr 1
        exact setLIntegral_congr_fun hmReach hweightOnReach
      _ ≤ (∫⁻ sample in reach, localCharge sample ∂μ) + ∫⁻ sample in reach, arrivalCharge sample ∂μ :=
        add_le_add le_rfl hArrival
      _ = ∫⁻ sample in reach, localCharge sample + arrivalCharge sample ∂μ := (lintegral_add_left hmLocal _).symm
      _ = ∫⁻ sample in reach, totalCharge sample ∂μ := setLIntegral_congr_fun hmReach (fun sample hs => (hchargeOnReach sample hs).symm)
  have hnoReachBound : (∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ) ≤
      ∫⁻ sample in reachᶜ, totalCharge sample ∂μ := by
    apply setLIntegral_mono' hmReach.compl
    intro sample hs
    have hnever : ∀ n, (run input C .uncapped accounting policy.val.rule sample n).cursor ≠ 1 := by
      intro n hc
      apply hs
      refine ⟨Set.mem_univ sample.1, n, ?_⟩
      rw [hnext]
      exact hc
    exact nativeHead_no_entry_charge_lower input C accounting policy.val.rule policy.val.legal head hhead next hnext sample hnever R price hprice
  rw [penaltyObjective_eq_lintegral_runPenaltyCharge input C .uncapped accounting policy.val.rule policy.val.measurable_rule]
  change (∫⁻ sample, localCharge sample + weight sample ∂μ) ≤ ∫⁻ sample, totalCharge sample ∂μ
  calc
    _ = (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) + ∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ :=
      (lintegral_add_compl _ hmReach).symm
    _ ≤ (∫⁻ sample in reach, totalCharge sample ∂μ) + ∫⁻ sample in reachᶜ, totalCharge sample ∂μ := add_le_add hreachBound hnoReachBound
    _ = _ := lintegral_add_compl _ hmReach

/-- Complete arbitrary-policy head lower inequality, including the genuine
one-stage terminal boundary. The source comparator and all failure charges
are unchanged; the final scalar localValue infimum is a separate step. -/
theorem nativeHead_allPolicy_lower (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentAllocation) (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : I.Stage) (hhead : head.val = 0) (price : ℝ) (hprice : 0 ≤ price) :
    (∫⁻ sample, (input.experiment head).observationCharge
        (headExitStop input head policy.val.rule sample.1 (worldTapes input sample.2 head)) +
      nativeHeadContinuationWeight input head R price policy.val.rule sample ∂input.seededWorldLaw ν) ≤
      penaltyObjective input C .uncapped accounting policy.val.rule ν (ENNReal.ofReal price) := by
  by_cases ht : I.stageCount ≤ 1
  · rw [penaltyObjective_eq_lintegral_runPenaltyCharge input C .uncapped accounting policy.val.rule policy.val.measurable_rule]
    exact lintegral_mono (fun sample => nativeHead_terminal_charge_lower input C accounting R policy head hhead ht sample price hprice)
  · let next : I.Stage := ⟨1, Nat.lt_of_not_ge ht⟩
    exact nativeHead_integrated_lower input C hC accounting R policy ν head next hhead rfl price hprice

end PaperProofs.Common.Native
