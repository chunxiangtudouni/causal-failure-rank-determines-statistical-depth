module

public import PaperProofs.Paid.PDMenu_PaidHeadIntegratedLower_055
public import PaperProofs.Paid.PDMenu_PaidTerminalLower_053

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Complete every-n original actual-policy local testing lower bound,
including singleton tasks, failures, nonreturn and arbitrary private seeds. -/
theorem paidFresh_allPolicy_local_lower (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ)
    (hn : 0 < n) (C : Contract (freshInstance n k)) (hC : C.IsCurrentPayment)
    (accounting : NormalAccounting (freshInstance n k))
    (policy : Policy (P.freshInput n k fee hfee) C .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (head : (freshInstance n k).Stage) (hhead : head.val = 0) (penalty : ℝ≥0∞) :
    let input := P.freshInput n k fee hfee
    (∫⁻ sample, (input.experiment head).observationCharge
        (headExitStop input head policy.rule sample.1 (worldTapes input sample.2 head)) +
      paidHeadContinuationWeight input head policy.rule
        (P.paidGoodSuccessor fee hfee n k penalty) (P.paidBadSuccessor fee hfee n k penalty) sample
      ∂input.seededWorldLaw ν) ≤ paidPenaltyObjective input C accounting policy.rule ν penalty := by
  intro input
  cases n with
  | zero => exact (Nat.not_lt_zero _ hn).elim
  | succ n =>
    cases n with
    | zero =>
      rw [paidPenaltyObjective_eq_lintegral input C accounting policy.rule policy.measurable_rule]
      exact lintegral_mono (fun sample => paidFresh_terminal_charge_lower P fee hfee k C accounting policy
        head hhead sample penalty)
    | succ n =>
      let next : (freshInstance (n + 1 + 1) k).Stage := ⟨1, by simp [freshInstance]⟩
      exact paidFresh_integrated_lower P fee hfee (n + 1) k C hC accounting policy ν head next hhead rfl penalty

end PDMenu

