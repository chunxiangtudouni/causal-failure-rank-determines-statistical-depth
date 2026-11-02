module

public import PaperProofs.Paid.PDROC_Simulator_007

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem rocEndpoint_decision_signed_at_stop
    (Q : PaperProofs.Statistics.BinarySymmetric.Parameters) (m : ℕ) (hm : m ≠ 0)
    (coin : Bool) (tape : Q.experiment.Tape) (n : ℕ)
    (hs : (Q.rocEndpointTest m).rule.stop coin tape = (n : ℕ∞)) :
    (Q.rocEndpointTest m).rule.decision coin tape = decide (0 ≤ Q.signedSum tape n) := by
  rw [rocEndpointTest, ite_eq_right hm] at hs
  change (Q.symmetricHittingTest m).rule.stop () tape = (n : ℕ∞) at hs
  have hd := (Q.experiment.posteriorSPRT_isPosteriorThresholdRule (Q.endpointError m)).2 tape n hs
  change (Q.symmetricHittingTest m).rule.decision () tape = _ at hd
  have hreal : (0 ≤ Q.experiment.logOddsScore tape n) ↔ (0 ≤ Q.signedSum tape n) := by
    rw [Q.logOddsScore_eq_signed, mul_nonneg_iff_of_pos_left Q.h_pos]
    constructor <;> intro h <;> exact_mod_cast h
  have heq : (Q.rocEndpointTest m).rule.decision coin tape =
      decide (0 ≤ Q.experiment.logOddsScore tape n) := by
    simpa only [rocEndpointTest, hm, ↓reduceIte, hittingTestOnBool] using hd
  rw [heq]
  simp only [hreal]

/-- At every proper pre-exit word, the actual concrete controller makes a
real review; no posterior-performance premise or source MAP assumption is used. -/
theorem simulatorBoundaryAction_before_endpoint (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (record : AuxiliaryRecord) (coin decision : Bool) (hd : record.decision = some decision)
    (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hbefore : (n : ℕ∞) < (P.binarySymmetric.rocEndpointTest record.level).rule.stop coin tape) :
    simulatorBoundaryAction history stage record coin = .review stage := by
  have hm : record.level ≠ 0 := by
    intro hzero
    have hz : (n : ℕ∞) < 0 := by
      simpa only [hzero, rocEndpointTest_zero, fairGuessTest] using hbefore
    exact (not_lt_of_ge (show (0 : ℕ∞) ≤ n from zero_le)) hz
  have hnot : ¬ record.level ≤ (P.binarySymmetric.signedSum tape n).natAbs := by
    intro hhit
    have hle := (P.binarySymmetric.symmetricHittingTest_stop_le_iff record.level tape n).mpr ⟨n, le_rfl, hhit⟩
    have hbefore' : (n : ℕ∞) < (P.binarySymmetric.symmetricHittingTest record.level).rule.stop () tape := by
      simpa only [rocEndpointTest, hm, ↓reduceIte, hittingTestOnBool] using hbefore
    exact (not_le_of_gt hbefore') hle
  simp only [simulatorBoundaryAction, hd, hm, ↓reduceIte, hscore, hnot]

/-- At the genuine finite endpoint stop the simulator writes exactly the
source decision transported by orientation xor the actual endpoint guess. -/
theorem simulatorBoundaryAction_at_endpoint (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (record : AuxiliaryRecord) (coin decision : Bool) (hd : record.decision = some decision)
    (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hs : (P.binarySymmetric.rocEndpointTest record.level).rule.stop coin tape = (n : ℕ∞)) :
    simulatorBoundaryAction history stage record coin =
      .write stage (Bool.xor decision (Bool.xor record.orientation
        ((P.binarySymmetric.rocEndpointTest record.level).rule.decision coin tape))) := by
  by_cases hm : record.level = 0
  · simp only [simulatorBoundaryAction, hd, hm, ↓reduceIte, rocEndpointTest_zero, fairGuessTest]
  · have hs' : (P.binarySymmetric.symmetricHittingTest record.level).rule.stop () tape = (n : ℕ∞) := by
      simpa only [rocEndpointTest, hm, ↓reduceIte, hittingTestOnBool] using hs
    have hhit : record.level ≤ (P.binarySymmetric.signedSum tape n).natAbs :=
      (P.binarySymmetric.symmetricHittingTest_hits_exact record.level (Nat.one_le_iff_ne_zero.mpr hm) tape n hs').ge
    rw [rocEndpoint_decision_signed_at_stop P.binarySymmetric record.level hm coin tape n hs]
    simp only [simulatorBoundaryAction, hd, hm, ↓reduceIte, hscore, hhit]

end PDROC
