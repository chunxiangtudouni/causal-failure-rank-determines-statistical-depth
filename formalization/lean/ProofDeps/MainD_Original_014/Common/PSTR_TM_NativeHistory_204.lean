module
public import Common.PSTR_TM_Length_004
public import PaperProofs.Common.NativeHorizon

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeHistory204
open PaperProofs.Common.Native
variable {I : Instance}

/-- Actual raw response count, including a possible late batch of all
stage reports. This avoids confusing historyActions with raw history.
The weaker general bound suffices for a polynomial in arithmeticScale. -/
theorem writeResponses_length_le (C : Contract I) (s : State I) (i : I.Stage) (bit : Bool) :
    (writeResponses C s i bit).length ≤ I.stageCount + 1 := by
  classical
  have hi : 1 ≤ I.stageCount := by
    have hi : i.val < I.stageCount := i.isLt
    omega
  simp only [writeResponses,List.length_append]
  split_ifs
  · simp only [List.length_cons,List.length_nil]
    omega
  · simp only [List.length_cons,List.length_nil,reportAll,List.length_ofFn]
    change 1 + I.stageCount ≤ I.stageCount + 1
    omega
  · simp only [List.length_cons,List.length_nil]
    omega

theorem step_history_length_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I}
    (h : Step input C mode accounting tapes s action next) :
    next.history.length ≤ s.history.length + (I.stageCount + 1) := by
  classical
  cases h <;> simp only [record,stopState,List.length_append,List.length_cons,List.length_nil]
  all_goals first
    | omega
    | exact Nat.add_le_add_left (writeResponses_length_le _ _ _ _) _

/-- Every original actual Prefix, every reporting mode and failed path.
No early-report qualification or equality of action/raw lengths is assumed. -/
theorem prefix_history_length_le (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : Nat} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s) :
    s.history.length ≤ (I.stageCount + 1)*s.clock := by
  induction hp with
  | initial => exact Nat.zero_le _
  | @next n s next _ step ih =>
    have hs := step_history_length_le input C mode accounting tapes step
    have hc := PaperProofs.Common.Native.step_clock input C mode accounting tapes step
    calc
      next.history.length ≤ s.history.length + (I.stageCount + 1) := hs
      _ ≤ (I.stageCount + 1)*s.clock + (I.stageCount + 1) := Nat.add_le_add_right ih _
      _ = (I.stageCount + 1)*next.clock := by rw [hc,Nat.mul_add,Nat.mul_one]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMNativeHistory204
