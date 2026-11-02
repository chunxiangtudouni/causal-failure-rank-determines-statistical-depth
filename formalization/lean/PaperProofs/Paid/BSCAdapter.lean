module

public import PaperProofs.Paid.Model
public import PaperProofs.Statistics.SymmetricHitting
public import PaperProofs.Statistics.SymmetricHittingExact
public import PaperProofs.Statistics.BSCStoppedPosterior

/-! Exact one-way adapter from the original paid input to neutral BSC tools. -/

@[expose] public section

namespace PaperProofs.Paid.Parameters

open scoped ENNReal

universe u

def binarySymmetric (P : PaperProofs.Paid.Parameters) :
    PaperProofs.Statistics.BinarySymmetric.Parameters where
  gamma := P.certificate.gamma
  gamma_pos := P.certificate.gamma_pos
  gamma_le_quarter := P.certificate.gamma_le_quarter
  reviewFee := P.reviewFee
  reviewFee_pos := P.reviewFee_pos

theorem experiment_eq_binarySymmetric (P : PaperProofs.Paid.Parameters) :
    P.experiment = P.binarySymmetric.experiment := rfl

theorem rocError_eq_endpointError (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.certificate.rocError m = P.binarySymmetric.endpointError m := rfl

theorem informationConstant_eq (P : PaperProofs.Paid.Parameters) :
    P.kappa = P.binarySymmetric.kappa := rfl

theorem priceCoefficient_eq (P : PaperProofs.Paid.Parameters) :
    P.a = P.binarySymmetric.a := rfl

/-- Exact stopping-test performance for the original paid experiment,
proved by the one-way adapter to the neutral BSC theorem below. -/
def SymmetricHittingExactLaw (P : PaperProofs.Paid.Parameters) : Prop :=
  P.binarySymmetric.SymmetricHittingExactLaw

theorem symmetricHittingExactLaw (P : PaperProofs.Paid.Parameters) : P.SymmetricHittingExactLaw :=
  P.binarySymmetric.symmetricHittingExactLaw

/-- The original paid experiment inherits the actual stopped-posterior
information identity, with arbitrary private-seed universes. -/
def StoppedPosteriorInformationIdentity (P : PaperProofs.Paid.Parameters) : Prop :=
  P.binarySymmetric.StoppedPosteriorInformationIdentity.{u}

theorem stoppedPosteriorInformationIdentity (P : PaperProofs.Paid.Parameters) :
    P.StoppedPosteriorInformationIdentity.{u} :=
  P.binarySymmetric.stoppedPosteriorInformationIdentity

/-- Restriction only to a seed/pre-birth event, with finiteness required
inside that event; the complement may have infinite expected sample count. -/
def PreBirthStoppedPosteriorInformationIdentity (P : PaperProofs.Paid.Parameters) : Prop :=
  P.binarySymmetric.PreBirthStoppedPosteriorInformationIdentity.{u}

theorem preBirthStoppedPosteriorInformationIdentity (P : PaperProofs.Paid.Parameters) :
    P.PreBirthStoppedPosteriorInformationIdentity.{u} :=
  P.binarySymmetric.preBirthStoppedPosteriorInformationIdentity

theorem bscSPRT_bayesObservationCharge_le (P : PaperProofs.Paid.Parameters) (p : ℚ)
    (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    P.experiment.bayesObservationCharge (MeasureTheory.Measure.dirac ()) (P.experiment.posteriorSPRT p) ≤
      ENNReal.ofReal (P.a * (Real.log (1 / (p : ℝ)) + P.h)) :=
  P.binarySymmetric.bscSPRT_bayesObservationCharge_le p hp hhalf

end PaperProofs.Paid.Parameters
