module

public import PaperProofs.Paid.PDMenu_MenuCompilerComplete_129
public import PaperProofs.Paid.MultiplierSearch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

/-- An analysis-only constant table of the original blind endpoint actions.
Its numerical fields are unused; no computed optimum is redefined. -/
def zeroChargeBlindEntry (fee : ℚ) : MenuEntry :=
  ⟨.test 0 (if fee = 0 then .repair else .abandon), 0, 0, 0⟩

def zeroChargeBlindTable (N K : ℕ) (fee : ℚ) : MenuTable :=
  Array.replicate (N+1) (Array.replicate (K+1) (zeroChargeBlindEntry fee))

theorem zeroChargeBlindTable_entry (N K : ℕ) (fee : ℚ) (n k : ℕ)
    (hn : n ≤ N) (hk : k ≤ K) :
    menuEntryAt (zeroChargeBlindTable N K fee) n k = zeroChargeBlindEntry fee := by
  have hn' : n < (Array.replicate (N+1) (Array.replicate (K+1) (zeroChargeBlindEntry fee))).size := by
    simp only [Array.size_replicate]; omega
  have hk' : k < (Array.replicate (K+1) (zeroChargeBlindEntry fee)).size := by
    simp only [Array.size_replicate]; omega
  have hr : (Array.replicate (N+1) (Array.replicate (K+1) (zeroChargeBlindEntry fee))).getD n #[] =
      Array.replicate (K+1) (zeroChargeBlindEntry fee) :=
    (Array.getElem_eq_getD (h := hn') #[]).symm.trans (Array.getElem_replicate hn')
  change ((Array.replicate (N+1) (Array.replicate (K+1) (zeroChargeBlindEntry fee))).getD n #[]).getD k abandonEntry = _
  rw [hr]
  exact (Array.getElem_eq_getD (h := hk') abandonEntry).symm.trans (Array.getElem_replicate hk')

def zeroChargeGenericCandidate (P : Parameters) (N K : ℕ) (fee : ℚ) :
    PolicyRule (freshInstance N K) (MenuSeed N K) :=
  fun seed history =>
    if historyHalted history then .stop else
    if hc : historyCursor history < N then
      let stage : (freshInstance N K).Stage := ⟨historyCursor history, by simpa [freshInstance] using hc⟩
      match historyWrite history stage with
      | none => .write stage (seed stage)
      | some (bit, serial) => match historyReport history stage with
        | none => .abandon
        | some (truth, reportedSerial) =>
            if serial != reportedSerial then .abandon else if bit == truth then .advance stage else
              if fee=0 then P.menuRepairAction N K history stage else .abandon
    else if historyCursor history=N then .stop else .abandon

theorem zeroChargeGeneric_eq_blindTable (P : Parameters) (N K : ℕ) (fee : ℚ)
    (seed : MenuSeed N K) (history : List (VisibleEvent (freshInstance N K))) :
    zeroChargeGenericCandidate P N K fee seed history =
      P.menuCandidateAction N K (zeroChargeBlindTable N K fee) seed history := by
  by_cases hh : historyHalted history = true
  · simp only [zeroChargeGenericCandidate, Parameters.menuCandidateAction, hh, ite_true]
  · rw [zeroChargeGenericCandidate, Parameters.menuCandidateAction, ite_eq_right hh, ite_eq_right hh]
    by_cases hc : historyCursor history < N
    · rw [dite_eq_left hc, dite_eq_left hc]
      dsimp only
      let stage : (freshInstance N K).Stage := ⟨historyCursor history, by simpa [freshInstance] using hc⟩
      have ht := zeroChargeBlindTable_entry N K fee
        (N-stage.val) (P.menuEntryTools N K history stage)
        (Nat.sub_le _ _) (Nat.sub_le _ _)
      change (match historyWrite history stage with
        | none => .write stage (seed stage)
        | some (bit, serial) => match historyReport history stage with
          | none => .abandon
          | some (truth, reportedSerial) =>
              if serial != reportedSerial then .abandon else if bit == truth then .advance stage else
                if fee = 0 then P.menuRepairAction N K history stage else .abandon : Action (freshInstance N K)) = _
      rw [ht]
      dsimp only [zeroChargeBlindEntry]
      cases hw : historyWrite history stage with
      | none => exact (P.endpointTestingAction_zero N K seed history stage).symm
      | some pair =>
          obtain ⟨bit,serial⟩ := pair
          dsimp only
          cases hr : historyReport history stage with
          | none => rfl
          | some packet =>
              obtain ⟨truth, reportedSerial⟩ := packet
              dsimp only
              split_ifs <;> rfl
    · rw [dite_eq_right hc, dite_eq_right hc]

/-- Equality for every visible history, including malformed ones. The
shared-instance aliases are compared by kernel definitional equality. -/
theorem zeroChargeCandidate_eq_blindTable (P : Parameters) (fee : ℚ)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance)) :
    P.zeroChargeCandidateRule fee seed history =
      P.menuCandidateAction P.certificate.stages P.tools
        (zeroChargeBlindTable P.certificate.stages P.tools fee) seed history :=
  zeroChargeGeneric_eq_blindTable P P.certificate.stages P.tools fee seed history

theorem zeroChargeRule_eq_blindTable (P : Parameters) (fee : ℚ) :
    P.zeroChargeRule fee = P.compiledMenuRule P.certificate.stages P.tools
      (zeroChargeBlindTable P.certificate.stages P.tools fee) := by
  funext seed history
  unfold Parameters.zeroChargeRule searchGuardRule Parameters.compiledMenuRule
  rw [zeroChargeCandidate_eq_blindTable P fee seed history]
  rfl

end PDMenu
