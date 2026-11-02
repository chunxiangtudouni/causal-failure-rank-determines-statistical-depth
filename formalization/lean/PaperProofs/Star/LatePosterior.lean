module

public import PaperProofs.Common.NativePreReport
public import PaperProofs.Common.NativeObservedWords
public import PaperProofs.Common.NativeCostBound
public import PaperProofs.Statistics.BSCStoppedPosterior
public import PaperProofs.Star.Model

/-!
The actual pre-report record for frozen star-proofs.tex:58--87. The native
returned-action horizon is derived from original finite quotas. The record
contains the private seed and only the event prefix preceding the FIRST truth
report: in particular the final ordinary write in the same response packet
is retained, while reports and later abandonment/repair outcomes are removed.
No whole State (which contains hidden truth) is put into the private record.

The product-posterior and full-history lower bounds are exact pending Prop
definitions. They impose no MAP, success, finite-ET or feasibility condition
on native comparison policies. All fees stay in ENNReal.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Star.Parameters

open Common Common.Native
open Statistics.BinarySymmetric

universe u

/-- The fallback only totalizes invalid public strings. Actual native words
have the original alphabet; no stopped infinity is converted to an empty word. -/
def preReportWord (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    P.channel.experiment.StoppedWord :=
  if historyObservations history stage = [] then ⟨0, Fin.elim0⟩ else
  if hvalid : ∀ symbol ∈ historyObservations history stage,
      symbol < P.channel.experiment.alphabetSize then
    ⟨(historyObservations history stage).length, fun k =>
      ⟨(historyObservations history stage)[k.val], hvalid _ (List.getElem_mem k.isLt)⟩⟩
  else ⟨0, Fin.elim0⟩

noncomputable def preReportPosteriorMass (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (truth : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (P.channel.wordPosteriorMass truth (P.preReportWord order history stage))

noncomputable def preReportMAPError (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) : ℝ :=
  P.channel.wordPosteriorError (P.preReportWord order history stage)

theorem preReportMAPError_pos (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) : 0 < P.preReportMAPError order history stage :=
  P.channel.wordPosteriorError_pos _

theorem preReportMAPError_le_half (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) : P.preReportMAPError order history stage ≤ 1 / 2 :=
  P.channel.wordPosteriorError_le_half _

theorem preReportMAPError_no_observations (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (hnil : historyObservations history stage = []) :
    P.preReportMAPError order history stage = 1 / 2 := by
  unfold preReportMAPError preReportWord
  rw [ite_eq_left hnil]
  exact P.channel.wordPosteriorError_empty

theorem preReportPosteriorMass_no_observations (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (hnil : historyObservations history stage = []) (truth : Bool) :
    P.preReportPosteriorMass order history stage truth = ENNReal.ofReal (1 / 2 : ℝ) := by
  unfold preReportPosteriorMass preReportWord
  rw [ite_eq_left hnil]
  norm_num [Statistics.BinarySymmetric.Parameters.wordPosteriorMass,
    Statistics.BinarySymmetric.Parameters.wordEvidence, Statistics.BinaryExperiment.wordProbability]

/-- Non-MAP writes are compared with the posterior MAP minimum, rather
than identifying their actual error with that minimum. -/
theorem preReportMAPError_le_decision (P : Star.Parameters) (order : Star.Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (bit : Bool) :
    ENNReal.ofReal (P.preReportMAPError order history stage) ≤
      P.preReportPosteriorMass order history stage (!bit) := by
  apply ENNReal.ofReal_le_ofReal
  cases bit
  · exact min_le_right _ _
  · exact min_le_left _ _

/-- C04. Conditional posterior factorization is stated on every measurable
record event, not just seed singletons and without assuming existence of an
arbitrary-seed regular conditional probability kernel. -/
def PreReportProductPosterior (P : Star.Parameters) : Prop :=
  ∀ (order : Star.Order) (C : Contract (starInstance P.tools order)), C.IsLateRetained →
    ∀ (accounting : NormalAccounting (starInstance P.tools order))
      (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input order) C .native accounting Seed,
          ∀ (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))), MeasurableSet B →
          ∀ truth : (starInstance P.tools order).Stage → Bool,
            (P.input order).seededWorldLaw ν
              {sample | preReportRecord (P.input order) C accounting policy.rule sample ∈ B ∧
                (P.input order).truthAt sample.2 = truth} =
              ∫⁻ record, B.indicator
                (fun record => ∏ stage, P.preReportPosteriorMass order record.2 stage (truth stage)) record
                ∂preReportLaw (P.input order) C accounting policy.rule ν

/-- The actual observation-information equality used before any
success-selection in C:77--87. This independent statement is proved in
NativeInformation from real native history and local stopped information. -/
def NativeLateObservationInformation (P : Star.Parameters) : Prop :=
  ∀ (order : Star.Order) (C : Contract (starInstance P.tools order)), C.IsLateRetained →
    ∀ (accounting : NormalAccounting (starInstance P.tools order))
      (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input order) C .native accounting Seed,
          expectedObservationBill (P.input order) C .native accounting policy.rule ν =
            ENNReal.ofReal P.channel.a *
              ∫⁻ record, ∑ stage, phi (P.preReportMAPError order record.2 stage)
                ∂preReportLaw (P.input order) C accounting policy.rule ν

/-- C05's conditional failure bound, including pre-report abandonment and
incomplete stopping. No future writes are filled into the actual record. -/
def PreReportFailureLower (P : Star.Parameters) : Prop :=
  ∀ (order : Star.Order) (C : Contract (starInstance P.tools order)), C.IsLateRetained →
    ∀ (accounting : NormalAccounting (starInstance P.tools order))
      (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input order) C .native accounting Seed,
          ∀ (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))), MeasurableSet B →
            (∫⁻ record, B.indicator
              (fun record => ∏ stage, ENNReal.ofReal (P.preReportMAPError order record.2 stage)) record
                ∂preReportLaw (P.input order) C accounting policy.rule ν) ≤
              (P.input order).seededWorldLaw ν
                {sample | preReportRecord (P.input order) C accounting policy.rule sample ∈ B ∧
                  ¬ runSuccess (P.input order) C .native accounting policy.rule sample}

/-- The cap-independent lower direction for every original native LR
contract and arbitrary private-seed/non-MAP/abandonment policy. -/
def NativeLateObservationLower (P : Star.Parameters) : Prop :=
  ∀ (order : Star.Order) (C : Contract (starInstance P.tools order)), C.IsLateRetained →
    ∀ (accounting : NormalAccounting (starInstance P.tools order))
      (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ (policy : Policy (P.input order) C .native accounting Seed) (delta : ℝ), 0 < delta →
          risk (P.input order) C .native accounting policy.rule ν ≤ ENNReal.ofReal delta →
            ENNReal.ofReal (P.channel.a * Real.log delta⁻¹ -
              2 * P.channel.a * (P.tools + 1 : ℕ)) ≤
                expectedObservationBill (P.input order) C .native accounting policy.rule ν

def NativeLateLowerClaims (P : Star.Parameters) : Prop :=
  P.NativeLateObservationInformation.{u} ∧ P.PreReportFailureLower.{u} ∧ P.NativeLateObservationLower.{u}

end PaperProofs.Star.Parameters
