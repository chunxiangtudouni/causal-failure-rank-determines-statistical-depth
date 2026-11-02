module

public import PaperProofs.Paid.PDMenu_PaidRecordBranches_054
public import PaperProofs.Paid.PDMenu_PaidHeadWeights_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open EntryContinuationPartition

variable {Seed : Type*} [MeasurableSpace Seed]

/-- The actual local charge plus the paid good/bad successors is dominated
by the original full paid objective on the exhaustive entry-record partition
and its genuine failure complement. No future history enters the seed. -/
theorem paidFresh_integrated_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (C : Contract (freshInstance (n + 1) k)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance (n + 1) k))
    (policy : Policy (P.freshInput (n + 1) k fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head next : (freshInstance (n + 1) k).Stage) (hhead : head.val = 0) (hnext : next.val = 1)
    (penalty : ℝ≥0∞) :
    let input := P.freshInput (n + 1) k fee hfee
    (∫⁻ sample, (input.experiment head).observationCharge
        (headExitStop input head policy.rule sample.1 (worldTapes input sample.2 head)) +
      paidHeadContinuationWeight input head policy.rule
        (P.paidGoodSuccessor fee hfee (n + 1) k penalty) (P.paidBadSuccessor fee hfee (n + 1) k penalty) sample
      ∂input.seededWorldLaw ν) ≤ paidPenaltyObjective input C accounting policy.rule ν penalty := by
  intro input
  let μ := input.seededWorldLaw ν
  let reach := reachGate input C .uncapped accounting policy.rule next Set.univ
  let localCharge := fun sample : Seed × input.World => (input.experiment head).observationCharge
    (headExitStop input head policy.rule sample.1 (worldTapes input sample.2 head))
  let weight := paidHeadContinuationWeight input head policy.rule
    (P.paidGoodSuccessor fee hfee (n + 1) k penalty) (P.paidBadSuccessor fee hfee (n + 1) k penalty)
  let total := runPaidPenaltyCharge input C accounting policy.rule penalty
  have hmReach : MeasurableSet reach := measurableSet_reachGate input C .uncapped accounting policy.rule
    policy.measurable_rule next Set.univ MeasurableSet.univ
  have hrow (record : Record (freshInstance (n + 1) k)) :
      (∫⁻ sample in indexedEvent input C .uncapped accounting policy.rule next Set.univ record,
        localCharge sample + weight sample ∂μ) ≤
      ∫⁻ sample in indexedEvent input C .uncapped accounting policy.rule next Set.univ record, total sample ∂μ := by
    let entryCost := startupObservationCharge input record.2 + paidEntryContinuationWeight head record.2
      (P.paidGoodSuccessor fee hfee (n + 1) k penalty) (P.paidBadSuccessor fee hfee (n + 1) k penalty)
    have hmRecord : MeasurableSet (indexedEvent input C .uncapped accounting policy.rule next Set.univ record) :=
      measurableSet_recordEvent input C .uncapped accounting policy.rule policy.measurable_rule next
        record.1 record.2 Set.univ MeasurableSet.univ
    have heq sample (hs : sample ∈ indexedEvent input C .uncapped accounting policy.rule next Set.univ record) :
        localCharge sample + weight sample = entryCost := by
      have hf := recordEvent_firstEntry input C .uncapped accounting policy.rule next record.1 record.2 Set.univ sample hs
      have hentry : FirstEntryAt input C .uncapped accounting policy.rule 1 record.1 sample :=
        ⟨hf.1.1.trans hnext, fun before hbefore hcursor => hf.1.2 before hbefore (hcursor.trans hnext.symm)⟩
      have hobs := firstEntry_one_prefix_observationBill input C accounting policy.rule policy.legal head hhead sample record.1 hentry
      have hstartup := congrArg (startupObservationCharge input) hf.2
      have hl : localCharge sample = startupObservationCharge input record.2 := hobs.symm.trans hstartup
      have hw := paidHeadContinuationWeight_on_entry input C hC.1.1 accounting policy.rule policy.legal
        head hhead sample record.1 hentry (P.paidGoodSuccessor fee hfee (n + 1) k penalty)
        (P.paidBadSuccessor fee hfee (n + 1) k penalty)
      rw [hf.2] at hw
      exact congrArg₂ (· + ·) hl hw
    calc
      _ = ∫⁻ _sample in indexedEvent input C .uncapped accounting policy.rule next Set.univ record, entryCost ∂μ :=
        setLIntegral_congr_fun hmRecord heq
      _ = _ := setLIntegral_const _ _
      _ ≤ _ := paidFresh_entry_record_lower P fee hfee n k C hC accounting policy ν head next hhead hnext
        record.1 record.2 Set.univ MeasurableSet.univ penalty
  have hreachBound : (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) ≤
      ∫⁻ sample in reach, total sample ∂μ := by
    rw [lintegral_eq_tsum_entry_records input C .uncapped accounting policy.rule policy.measurable_rule
      next Set.univ MeasurableSet.univ μ (fun sample => localCharge sample + weight sample),
      lintegral_eq_tsum_entry_records input C .uncapped accounting policy.rule policy.measurable_rule
      next Set.univ MeasurableSet.univ μ total]
    exact ENNReal.tsum_le_tsum hrow
  have hgood : P.paidGoodSuccessor fee hfee (n + 1) k penalty ≤ penalty :=
    P.freshPaidPenalty_le_penalty fee hfee n k penalty
  have hbad : P.paidBadSuccessor fee hfee (n + 1) k penalty ≤ penalty := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact min_le_left _ _
  have hnoReachBound : (∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ) ≤
      ∫⁻ sample in reachᶜ, total sample ∂μ := by
    apply setLIntegral_mono' hmReach.compl
    intro sample hs
    have hnever : ∀ clock, (run input C .uncapped accounting policy.rule sample clock).cursor ≠ 1 := by
      intro clock hc
      apply hs
      refine ⟨Set.mem_univ sample.1, clock, ?_⟩
      rw [hnext]
      exact hc
    exact paidHead_no_entry_charge_lower input C accounting policy.rule policy.legal head hhead next hnext sample hnever
      (P.paidGoodSuccessor fee hfee (n + 1) k penalty) (P.paidBadSuccessor fee hfee (n + 1) k penalty)
      penalty hgood hbad
  rw [paidPenaltyObjective_eq_lintegral input C accounting policy.rule policy.measurable_rule]
  change (∫⁻ sample, localCharge sample + weight sample ∂μ) ≤ ∫⁻ sample, total sample ∂μ
  calc
    _ = (∫⁻ sample in reach, localCharge sample + weight sample ∂μ) +
        ∫⁻ sample in reachᶜ, localCharge sample + weight sample ∂μ := (lintegral_add_compl _ hmReach).symm
    _ ≤ (∫⁻ sample in reach, total sample ∂μ) + ∫⁻ sample in reachᶜ, total sample ∂μ := add_le_add hreachBound hnoReachBound
    _ = _ := lintegral_add_compl _ hmReach

end PDMenu




