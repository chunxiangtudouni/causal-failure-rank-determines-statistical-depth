module

public import PaperProofs.Paid.PDMenu_PaidHeadWeights_049
public import PaperProofs.Paid.PDMenu_PaidPastExecutionCharge_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Exact original one-stage paid boundary, pathwise for every actual
policy. An allocated but unpaid head is never counted as repaired. -/
theorem paidFresh_terminal_charge_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (k : ℕ)
    (C : Contract (freshInstance 1 k)) (accounting : NormalAccounting (freshInstance 1 k))
    (policy : Policy (P.freshInput 1 k fee hfee) C .uncapped accounting Seed)
    (head : (freshInstance 1 k).Stage) (hhead : head.val = 0)
    (sample : Seed × (P.freshInput 1 k fee hfee).World) (penalty : ℝ≥0∞) :
    let input := P.freshInput 1 k fee hfee
    (input.experiment head).observationCharge
        (headExitStop input head policy.rule sample.1 (worldTapes input sample.2 head)) +
      paidHeadContinuationWeight input head policy.rule
        (P.paidGoodSuccessor fee hfee 1 k penalty) (P.paidBadSuccessor fee hfee 1 k penalty) sample ≤
      runPaidPenaltyCharge input C accounting policy.rule penalty sample := by
  classical
  intro input
  have hgood : P.paidGoodSuccessor fee hfee 1 k penalty = 0 :=
    P.freshPaidPenalty_empty fee hfee k penalty
  have hbadPenalty : P.paidBadSuccessor fee hfee 1 k penalty ≤ penalty := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact min_le_left _ _
  have hob := nativeHead_observationCharge_le input C accounting policy.rule head hhead sample
  have hobActual := hob.trans (runObservationBill_le_actual input C .uncapped accounting policy.rule sample)
  by_cases hcorrect : headExitDecision input head policy.rule sample.1 (worldTapes input sample.2 head) =
      input.truthAt sample.2 head
  · simp only [paidHeadContinuationWeight, hcorrect, ↓reduceIte, hgood, add_zero]
    exact hobActual.trans (le_self_add : runActualBill input C .uncapped accounting policy.rule sample ≤
      runPaidPenaltyCharge input C accounting policy.rule penalty sample)
  · simp only [paidHeadContinuationWeight, hcorrect, ↓reduceIte]
    by_cases hsuccess : runSuccess input C .uncapped accounting policy.rule sample
    · obtain ⟨clock, _hhalt, hs⟩ := hsuccess
      rcases hs.2.2.2 head with hright | ⟨e, he, _hstage⟩
      · have hw : (run input C .uncapped accounting policy.rule sample clock).ledger.written head =
            some (input.truthAt sample.2 head) := by
          rw [← run_truth input C .uncapped accounting policy.rule policy.legal sample clock]
          exact hright
        exact (hcorrect (nativeHead_decision_of_written input C accounting policy.rule policy.legal
          head hhead sample clock _ hw)).elim
      · have hbadFee : P.paidBadSuccessor fee hfee 1 k penalty ≤ ENNReal.ofReal (fee : ℝ) := by
          cases k with
          | zero => exact Fin.elim0 e.tool
          | succ k =>
            simpa only [Parameters.paidBadSuccessor, Nat.sub_self, Parameters.freshPaidPenalty_empty, add_zero] using
              (min_le_right penalty (ENNReal.ofReal (fee : ℝ)))
        have hfeeFull := runObservationBill_add_actualFee_le input C .uncapped accounting policy.rule
          policy.legal sample clock e he fee (fun _ _ => rfl)
        exact ((add_le_add hob hbadFee).trans hfeeFull).trans
          (le_self_add : runActualBill input C .uncapped accounting policy.rule sample ≤
            runPaidPenaltyCharge input C accounting policy.rule penalty sample)
    · unfold runPaidPenaltyCharge
      simp only [hsuccess, ↓reduceIte]
      exact add_le_add hobActual hbadPenalty

end PDMenu
