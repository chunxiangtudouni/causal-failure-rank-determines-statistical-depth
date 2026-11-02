module

public import PaperProofs.Paid.PDMenu_ZeroChargeBlindTable_143
public import PaperProofs.Common.NativeCapTransfer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

def positiveActionGeneric {I : Instance} (fee : ℚ) : Action I → Bool
  | .review _ => true
  | .execute _ _ => decide (0 < fee)
  | _ => false

theorem positiveActionGeneric_eq (P : Parameters) (fee : ℚ) (action : Action P.sharedInstance) :
    positiveActionGeneric fee action = P.isPositiveVariableAction fee action := by
  cases action <;> rfl

theorem zeroFee_menuRepairAction_noPositive (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K))) (stage : (freshInstance N K).Stage) :
    positiveActionGeneric 0 (P.menuRepairAction N K history stage) = false := by
  unfold Parameters.menuRepairAction
  split_ifs
  · rfl
  · split
    · simp [positiveActionGeneric]
    · split <;> rfl

theorem zeroChargeGeneric_noPositive (P : Parameters) (N K : ℕ) (fee : ℚ)
    (seed : MenuSeed N K) (history : List (VisibleEvent (freshInstance N K))) :
    positiveActionGeneric fee (zeroChargeGenericCandidate P N K fee seed history) = false := by
  unfold zeroChargeGenericCandidate
  by_cases hh : historyHalted history = true
  · rw [ite_eq_left hh]; rfl
  · rw [ite_eq_right hh]
    by_cases hc : historyCursor history < N
    · rw [dite_eq_left hc]
      dsimp only
      let stage : (freshInstance N K).Stage := ⟨historyCursor history, by simpa [freshInstance] using hc⟩
      cases hw : historyWrite history stage with
      | none => rfl
      | some pair =>
          obtain ⟨bit, serial⟩ := pair
          dsimp only
          cases hr : historyReport history stage with
          | none => rfl
          | some packet =>
              obtain ⟨truth, reportedSerial⟩ := packet
              dsimp only
              split_ifs with hs hb hf
              · rfl
              · rfl
              · subst fee
                exact zeroFee_menuRepairAction_noPositive P N K history stage
              · rfl
    · rw [dite_eq_right hc]
      split_ifs <;> rfl

theorem zeroChargeCandidate_noPositive (P : Parameters) (fee : ℚ)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance)) :
    P.isPositiveVariableAction fee (P.zeroChargeCandidateRule fee seed history) = false := by
  rw [← positiveActionGeneric_eq]
  exact zeroChargeGeneric_noPositive P P.certificate.stages P.tools fee seed history

theorem zeroChargeRule_noPositive (P : Parameters) (fee : ℚ)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance)) :
    P.isPositiveVariableAction fee (P.zeroChargeRule fee seed history) = false := by
  unfold Parameters.zeroChargeRule searchGuardRule
  dsimp only
  by_cases hc : historyAllowsAction history (P.zeroChargeCandidateRule fee seed history)
  · rw [ite_eq_left hc]
    exact zeroChargeCandidate_noPositive P fee seed history
  · rw [ite_eq_right hc]
    rfl

end PDMenu
