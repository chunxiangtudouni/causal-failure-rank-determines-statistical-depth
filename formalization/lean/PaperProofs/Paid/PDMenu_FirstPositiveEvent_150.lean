module

public import PaperProofs.Paid.PDMenu_FirstPositiveCensor_149
public import PaperProofs.Paid.PDROC_ZeroChargeLower_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem firstPositiveCensor_run_eq_of_not_mem (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed)
    (sample : Seed × (P.input fee hfee).World)
    (hnot : sample ∉ P.positiveChargeEvent fee hfee C mode accounting rule) (clock : ℕ) :
    run (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee rule) sample clock =
      run (P.input fee hfee) C.val mode accounting rule sample clock := by
  induction clock with
  | zero => rfl
  | succ n ih =>
      by_cases hh : (run (P.input fee hfee) C.val mode accounting rule sample n).halted = true
      · have hhc : (run (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee rule) sample n).halted = true := by
          rw [ih]; exact hh
        rw [run_succ_of_halted _ _ _ _ _ _ _ hhc, run_succ_of_halted _ _ _ _ _ _ _ hh, ih]
      · have ha := Bool.eq_false_iff.mpr hh
        have hpos : ¬P.isPositiveVariableAction fee
            (rule sample.1 (run (P.input fee hfee) C.val mode accounting rule sample n).history) = true := by
          intro hp
          exact hnot ⟨n, ha, hp⟩
        simp only [run, ih, firstPositiveCensorRule, ite_eq_right hpos]

theorem firstPositiveCensor_success_iff_of_not_mem (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed)
    (sample : Seed × (P.input fee hfee).World)
    (hnot : sample ∉ P.positiveChargeEvent fee hfee C mode accounting rule) :
    runSuccess (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee rule) sample ↔
      runSuccess (P.input fee hfee) C.val mode accounting rule sample := by
  simp only [runSuccess, firstPositiveCensor_run_eq_of_not_mem P fee hfee C mode accounting rule sample hnot]

theorem firstPositiveCensor_risk_le (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) :
    risk (P.input fee hfee) C.val mode accounting (firstPositiveCensorRule P fee rule) ν ≤
      risk (P.input fee hfee) C.val mode accounting rule ν +
        (P.input fee hfee).seededWorldLaw ν (P.positiveChargeEvent fee hfee C mode accounting rule) := by
  classical
  apply (measure_mono (show {sample | ¬runSuccess (P.input fee hfee) C.val mode accounting
      (firstPositiveCensorRule P fee rule) sample} ⊆
      {sample | ¬runSuccess (P.input fee hfee) C.val mode accounting rule sample} ∪
        P.positiveChargeEvent fee hfee C mode accounting rule from ?_)).trans (measure_union_le _ _)
  intro sample hc
  by_cases hp : sample ∈ P.positiveChargeEvent fee hfee C mode accounting rule
  · exact Or.inr hp
  · exact Or.inl (fun hs => hc ((firstPositiveCensor_success_iff_of_not_mem P fee hfee C mode accounting rule sample hp).mpr hs))

/-- The actual causal censor loses success only on the source's literal
first-positive-action event. Its zero expected bill is proved above. -/
theorem positiveChargeEvent_mass_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : Policy (P.input fee hfee) C.val mode accounting Seed)
    (hrisk : risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk) :
    ENNReal.ofReal ((P.zeroChargeRisk fee-P.certificate.risk : ℚ) : ℝ) ≤
      (P.input fee hfee).seededWorldLaw ν (P.positiveChargeEvent fee hfee C mode accounting policy.rule) := by
  let censored := firstPositiveCensorPolicy P fee hfee C mode accounting policy
  have hz := PDROC.ZeroChargeLower.originalZeroChargePolicyLower P fee hfee C accounting mode Seed
    inferInstance ν inferInstance censored (firstPositiveCensor_expectedBill P fee hfee C mode accounting policy ν)
  have hc := firstPositiveCensor_risk_le P fee hfee C mode accounting policy.rule ν
  have htotal : ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) ≤ P.targetRisk +
      (P.input fee hfee).seededWorldLaw ν (P.positiveChargeEvent fee hfee C mode accounting policy.rule) :=
    hz.trans (hc.trans (add_le_add hrisk le_rfl))
  have hd : (0:ℝ) ≤ (P.certificate.risk:ℝ) := by exact_mod_cast P.certificate.risk_pos.le
  rw [Rat.cast_sub, ENNReal.ofReal_sub _ hd]
  apply tsub_le_iff_right.mpr
  simpa only [PaperProofs.Paid.Parameters.targetRisk, add_comm] using htotal

end PDMenu
