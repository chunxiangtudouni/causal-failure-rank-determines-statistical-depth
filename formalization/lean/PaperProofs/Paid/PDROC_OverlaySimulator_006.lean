module

public import PaperProofs.Paid.PDROC_Simulator_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

/-- A canonical MAP-oriented record used only to reuse the already verified
Native endpoint controller. It does not replace the source auxiliary record. -/
def overlayMAPEndpointRecord (m : ℕ) : AuxiliaryRecord :=
  ⟨List.replicate m (1 : Fin 2), some true⟩

@[simp] theorem overlayMAPEndpointRecord_score (m : ℕ) :
    (overlayMAPEndpointRecord m).score = (m : ℤ) := by
  simp [overlayMAPEndpointRecord, AuxiliaryRecord.score]

@[simp] theorem overlayMAPEndpointRecord_level (m : ℕ) :
    (overlayMAPEndpointRecord m).level = m := by
  simp [AuxiliaryRecord.level]

@[simp] theorem overlayMAPEndpointRecord_orientation (m : ℕ) :
    (overlayMAPEndpointRecord m).orientation = true := by
  simp [AuxiliaryRecord.orientation]

def overlayMAPAction {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (m : ℕ) (coin : Bool) : Action I :=
  simulatorBoundaryAction history stage (overlayMAPEndpointRecord m) coin

theorem overlayMAPAction_before_endpoint (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (m : ℕ) (coin : Bool) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hbefore : (n : ℕ∞) < (P.binarySymmetric.rocEndpointTest m).rule.stop coin tape) :
    overlayMAPAction history stage m coin = .review stage := by
  apply simulatorBoundaryAction_before_endpoint P history stage (overlayMAPEndpointRecord m) coin true rfl tape n hscore
  simpa only [overlayMAPEndpointRecord_level] using hbefore

theorem overlayMAPAction_at_endpoint (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (m : ℕ) (coin : Bool) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hs : (P.binarySymmetric.rocEndpointTest m).rule.stop coin tape = (n : ℕ∞)) :
    overlayMAPAction history stage m coin =
      .write stage ((P.binarySymmetric.rocEndpointTest m).rule.decision coin tape) := by
  have h := simulatorBoundaryAction_at_endpoint P history stage (overlayMAPEndpointRecord m) coin true rfl tape n hscore
    (by simpa only [overlayMAPEndpointRecord_level] using hs)
  have hb (bit : Bool) : Bool.xor true (Bool.xor true bit) = bit := by cases bit <;> rfl
  simpa only [overlayMAPAction, overlayMAPEndpointRecord_level, overlayMAPEndpointRecord_orientation, hb] using h

def overlayMixtureEndpoint (m : ℕ) (coins : Bool × Bool) : ℕ := if coins.1 then m else m + 1

theorem adjacentMixture_stop_eq_endpoint
    (Q : PaperProofs.Statistics.BinarySymmetric.Parameters) (m : ℕ) (coins : Bool × Bool)
    (tape : Q.experiment.Tape) :
    (Q.adjacentMixtureTest m).rule.stop coins tape =
      (Q.rocEndpointTest (overlayMixtureEndpoint m coins)).rule.stop coins.2 tape := by
  cases h : coins.1 <;> simp [adjacentMixtureTest, overlayMixtureEndpoint, h]

theorem adjacentMixture_decision_eq_endpoint
    (Q : PaperProofs.Statistics.BinarySymmetric.Parameters) (m : ℕ) (coins : Bool × Bool)
    (tape : Q.experiment.Tape) :
    (Q.adjacentMixtureTest m).rule.decision coins tape =
      (Q.rocEndpointTest (overlayMixtureEndpoint m coins)).rule.decision coins.2 tape := by
  cases h : coins.1 <;> simp [adjacentMixtureTest, overlayMixtureEndpoint, h]

/-- The actual controller reads only the observed prefix and private coins.
The selected adjacent endpoint is fixed before the actual tape is opened. -/
def overlayMixtureAction {I : Instance} (history : List (VisibleEvent I))
    (stage : I.Stage) (m : ℕ) (coins : Bool × Bool) : Action I :=
  overlayMAPAction history stage (overlayMixtureEndpoint m coins) coins.2

theorem overlayMixtureAction_before_stop (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (m : ℕ) (coins : Bool × Bool) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hbefore : (n : ℕ∞) < (P.binarySymmetric.adjacentMixtureTest m).rule.stop coins tape) :
    overlayMixtureAction history stage m coins = .review stage := by
  exact overlayMAPAction_before_endpoint P history stage _ _ tape n hscore
    (by simpa only [adjacentMixture_stop_eq_endpoint] using hbefore)

theorem overlayMixtureAction_at_stop (P : PaperProofs.Paid.Parameters)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage)
    (m : ℕ) (coins : Bool × Bool) (tape : P.binarySymmetric.experiment.Tape) (n : ℕ)
    (hscore : simulatorObservedScore history stage = P.binarySymmetric.signedSum tape n)
    (hs : (P.binarySymmetric.adjacentMixtureTest m).rule.stop coins tape = (n : ℕ∞)) :
    overlayMixtureAction history stage m coins =
      .write stage ((P.binarySymmetric.adjacentMixtureTest m).rule.decision coins tape) := by
  rw [adjacentMixture_decision_eq_endpoint]
  exact overlayMAPAction_at_endpoint P history stage _ _ tape n hscore
    (by simpa only [adjacentMixture_stop_eq_endpoint] using hs)

end PDROC
