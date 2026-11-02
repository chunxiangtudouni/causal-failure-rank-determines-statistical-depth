module

public import PaperProofs.Common.NativeHeadAccounting

/-! The actual one-stage boundary of the B08 arbitrary-policy lower bound.
Absent repair permission is handled by real UsesOnly and allocation guards. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance} {Seed : Type*} [MeasurableSpace Seed]

/-- When no R-permitted tool can repair the head, ORIGINAL success forces
the extracted possibly non-MAP local decision to be correct. -/
theorem nativeHead_no_repair_success_correct (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (head : I.Stage) (hhead : head.val = 0)
    (hempty : I.eligible head ∩ R = ∅) (sample : Seed × input.World)
    (hsuccess : runSuccess input C .uncapped accounting policy.val.rule sample) :
    headExitDecision input head policy.val.rule sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head := by
  obtain ⟨n, _, hs⟩ := hsuccess
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample n
  rcases hs.2.2.2 head with hc | ⟨e, he, hes⟩
  · have hw : (run input C .uncapped accounting policy.val.rule sample n).ledger.written head = some (input.truthAt sample.2 head) := by
      rw [← run_truth input C .uncapped accounting policy.val.rule policy.val.legal sample n]
      exact hc
    exact nativeHead_decision_of_written input C accounting policy.val.rule policy.val.legal head hhead sample n _ hw
  · have hwf := run_ledgerWellFormed input C .uncapped accounting policy.val.rule policy.val.legal sample n
    obtain ⟨a, ha, hh, _, _⟩ := hwf.backed e he
    have hu := prefix_commitments_usable input C accounting policy.val.rule R policy.property sample.1 _ _ hp a ha
    have hstage : a.handle.stage = head := (congrArg MismatchHandle.stage hh).trans hes
    rw [hstage] at hu
    have hm : a.tool ∈ I.eligible head ∩ R := Finset.mem_inter.mpr ⟨hu.2, hu.1⟩
    rw [hempty] at hm
    exact (Finset.notMem_empty _ hm).elim

/-- Complete one-stage boundary: the same local charge plus independently
defined Gg/Gb weight is paid by any R-legal original policy, pathwise. -/
theorem nativeHead_terminal_charge_lower (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (R : Finset I.Tool)
    (policy : AvailablePolicy input C accounting R Seed) (head : I.Stage) (hhead : head.val = 0)
    (hterminal : I.stageCount ≤ 1) (sample : Seed × input.World) (price : ℝ) (hprice : 0 ≤ price) :
    (input.experiment head).observationCharge
        (headExitStop input head policy.val.rule sample.1 (worldTapes input sample.2 head)) +
      nativeHeadContinuationWeight input head R price policy.val.rule sample ≤
      runPenaltyCharge input C .uncapped accounting policy.val.rule (ENNReal.ofReal price) sample := by
  classical
  have hgood : input.goodPenaltyReal head R price = 0 := by
    unfold StatisticalInput.goodPenaltyReal
    apply input.healthyPenaltyReal_terminal
    simpa only [hhead, Nat.zero_add] using hterminal
  have hob := nativeHead_observationCharge_le input C accounting policy.val.rule head hhead sample
  by_cases hrepair : (I.eligible head ∩ R).Nonempty
  · have hbad : input.badPenaltyReal head R price = 0 := by
      simp only [StatisticalInput.badPenaltyReal, hrepair, ↓reduceDIte]
      have hf : (fun tool : I.Tool => input.healthyPenaltyReal (head.val + 1) (R.erase tool) price) = fun _ => 0 := by
        funext tool
        apply input.healthyPenaltyReal_terminal
        simpa only [hhead, Nat.zero_add] using hterminal
      rw [hf]
      exact Finset.inf'_const _ _
    have hw : nativeHeadContinuationWeight input head R price policy.val.rule sample = 0 := by
      unfold nativeHeadContinuationWeight
      split <;> simp only [hgood, hbad, ENNReal.ofReal_zero]
    rw [hw, add_zero]
    apply hob.trans
    unfold runPenaltyCharge
    exact le_add_of_nonneg_right bot_le
  · have hempty : I.eligible head ∩ R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hrepair
    by_cases hs : runSuccess input C .uncapped accounting policy.val.rule sample
    · have hc := nativeHead_no_repair_success_correct input C accounting R policy head hhead hempty sample hs
      simp only [nativeHeadContinuationWeight, hc, ↓reduceIte, hgood, ENNReal.ofReal_zero, add_zero,
        runPenaltyCharge, hs]
      exact hob
    · have hw := nativeHeadContinuationWeight_le_penalty input head R price hprice policy.val.rule sample
      unfold runPenaltyCharge
      simp only [hs, ↓reduceIte]
      exact add_le_add hob hw

end PaperProofs.Common.Native
