module

public import PaperProofs.Paid.PDROC_SimulatorLaw_019
public import PaperProofs.Paid.PDROC_RepresentationAssembly_002
public import PaperProofs.Paid.PDROC_Infima_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- Complete ORIGINAL boundary representation for the actual concrete
simulator. All history, record-cell, stage-flow, observation, correction
fee-law and risk obligations have been proved and discharged. -/
theorem simulatorBoundaryRepresentation
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    P.BoundaryRepresentation fee hfee C accounting ν (simulatorSeedLaw P ν) source
      (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule) :=
  simulatorBoundaryRepresentation_of_history_observation P fee hfee C accounting source ν hfinite
    (simulatorSourceHistoryLaw P fee hfee C accounting source ν hfinite)
    (simulator_observation_le_source P fee hfee C accounting source ν hfinite)

/-- Original D06 record representation, with every original mode and
private-seed universe and all ENNReal penalties, including infinity. -/
theorem recordRepresentationClaims (P : Parameters) : P.RecordRepresentationClaims.{u} := by
  apply recordRepresentationClaims_of_nativeRepresentation P
  intro fee hfee C accounting Seed ms ν hν source hfinite
  let : MeasurableSpace Seed := ms
  let : IsProbabilityMeasure ν := hν
  exact simulatorBoundaryRepresentation P fee hfee C accounting source ν hfinite

/-- Original full-policy infimum statement, preserving infinite objectives
and the arbitrary universe of the representation subclass. -/
theorem representationAtPenaltyInfima (P : Parameters) : P.RepresentationAtPenaltyInfima.{u} :=
  representationAtPenaltyInfima_of_recordRepresentation P (recordRepresentationClaims P)

/-- Complete ORIGINAL D06 target. No simulator-performance, source-law,
entry-flow, observation-comparison, finite-ET or MAP premise remains. -/
theorem firstFailureRepresentationClaims (P : Parameters) : P.FirstFailureRepresentationClaims.{u} :=
  ⟨recordRepresentationClaims P, representationAtPenaltyInfima P⟩

end PDROC
