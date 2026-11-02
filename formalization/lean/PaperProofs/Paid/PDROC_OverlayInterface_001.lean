module

public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC.OverlayDraft

universe u v

/-- D14-specific selectors are applied AFTER its auxiliary record is known.
The old D06 data and every already proved interface remain unchanged.
Only record is needed: both target and false-positive weight are functions
of it; the old virtual entry is used upstream to select that record. -/
structure OverlaySimulatorData (I : Instance) (SourceSeed : Type u) (SimSeed : Type v)
    extends RecordSimulatorData I SourceSeed SimSeed where
  mixtureCoinsAtRecord : SimSeed → I.Stage → AuxiliaryRecord → Bool × Bool
  falsePositiveCoinAtRecord : SimSeed → I.Stage → AuxiliaryRecord → Bool

def OverlaySimulatorMeasurable {I : Instance} {SourceSeed : Type u} {SimSeed : Type v}
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (data : OverlaySimulatorData I SourceSeed SimSeed) : Prop :=
  RecordSimulatorMeasurable data.toRecordSimulatorData ∧
    (∀ stage, Measurable (fun pair : SimSeed × AuxiliaryRecord =>
      data.mixtureCoinsAtRecord pair.1 stage pair.2)) ∧
    ∀ stage, Measurable (fun pair : SimSeed × AuxiliaryRecord =>
      data.falsePositiveCoinAtRecord pair.1 stage pair.2)

section Overlay

variable {SourceSeed : Type u} {SimSeed : Type v}

/-- Original D14 stage statement, changing only the lookup of the fresh
mixture seed at the realized record. No performance premise is added. -/
def OverlayStageRealization (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SimSeed] (ν : Measure SimSeed) (rule : PolicyRule P.sharedInstance SimSeed)
    (data : OverlaySimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
    ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
      let record := data.record sample.1 stage entry
      match record.decision with
      | none => P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage = none ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = 0
      | some _ =>
        let test := P.overlayRecordTest fee hfee record
        let tape := (P.input fee hfee).reviewAt sample.2 stage
        ∃ n : ℕ, test.rule.stop (data.mixtureCoinsAtRecord sample.1 stage record) tape = (n : ℕ∞) ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = (n : ℕ∞) ∧
          P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage =
            some (test.rule.decision (data.mixtureCoinsAtRecord sample.1 stage record) tape) ∧
          (if test.rule.decision (data.mixtureCoinsAtRecord sample.1 stage record) tape then
            0 ≤ P.binarySymmetric.experiment.logOddsScore tape n
           else P.binarySymmetric.experiment.logOddsScore tape n ≤ 0)

/-- Original all-path domination, genuine handle and physical-subsequence
requirements, changing only the selector at the already specified entry. -/
def OverlayPathCoupling (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : OverlaySimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  (∀ sample n,
    let actual := (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history
    let virtual := data.shadow sample.1 actual
    (reservedPairs actual).Sublist (reservedPairs virtual) ∧
    (executedPairs actual).Sublist (executedPairs virtual) ∧
    historyUsed actual ⊆ historyUsed virtual) ∧
  (∀ sample stage, P.actualWriteError fee hfee C accounting rule stage sample →
    P.virtualWriteError fee hfee C accounting rule data.toRecordSimulatorData stage sample) ∧
  (∀ sample stage entry decision,
    entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
    (data.record sample.1 stage entry).decision = some decision →
    (∃ n, (historyReport
      (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history stage).isSome = true) →
      (P.virtualWriteError fee hfee C accounting rule data.toRecordSimulatorData stage sample ↔
        P.actualWriteError fee hfee C accounting rule stage sample ∨
          data.falsePositiveCoinAtRecord sample.1 stage (data.record sample.1 stage entry) = true)) ∧
  (∀ sample n stage,
    let actual := (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history
    let virtual := data.shadow sample.1 actual
    (historyReport virtual stage).isSome = true →
      (historyReport actual stage).isSome = true ∧
      ∀ entry decision,
        entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
        (data.record sample.1 stage entry).decision = some decision →
        (historyReport virtual stage).map Prod.fst = some (Bool.xor decision
          (P.actualWriteErrorFlag fee hfee C accounting rule stage sample ||
            data.falsePositiveCoinAtRecord sample.1 stage (data.record sample.1 stage entry)))) ∧
  ∀ sample n,
    (run (P.input fee hfee) C.val .uncapped accounting rule sample n).ledger.executions.length ≤
      min P.certificate.stages P.tools

/-- The old record-cell definition already integrates the current fresh
coins rather than conditioning on the entire new seed. Its full contents
are preserved by the base projection. -/
def OverlayRecordCells (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed] (ν : Measure SimSeed)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : OverlaySimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  P.OverlayRecordCells fee hfee C accounting ν rule data.toRecordSimulatorData

/-- Encoding-correction candidate for the original D14 witness. Risk,
success, complete shadow law, nonreturn, and every all-path bill conclusion
are unchanged. This declaration is a target, not a proved construction. -/
def VirtualOverlayRepresentation (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : OverlaySimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  OverlaySimulatorMeasurable data ∧ P.ShadowCausal data.toRecordSimulatorData ∧
    P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data.toRecordSimulatorData ∧
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule
      data.toRecordSimulatorData ∧
    OverlayStageRealization P fee hfee C accounting νactual actual.rule data ∧
    OverlayPathCoupling P fee hfee C accounting actual.rule data ∧
    OverlayRecordCells P fee hfee C accounting νactual actual.rule data ∧
    (P.input fee hfee).seededWorldLaw νactual
      {sample | completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0 ∧
    (∀ sample n,
      let virtual := data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, PaperProofs.Paid.Parameters.historyStageResolved P.sharedInstance virtual stage = true) →
        runSuccess (P.input fee hfee) C.val .uncapped accounting actual.rule sample) ∧
    risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      risk (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource ∧
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource +
        P.overlayObservationIncrement fee ∧
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting actual.rule νactual ≤ P.overlayCorrectionAmount fee ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input 0 (by norm_num)) C.val .uncapped accounting source.rule νsource +
        P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee

end Overlay

/-- Only the D14-specific witness data changes; all original universes,
policies, modes, finite-full-bill input and ENNReal penalties are preserved. -/
def VirtualErrorCouplingClaims (P : Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ original : Policy (P.input 0 (by norm_num)) C.val mode accounting Seed,
        expectedBill (P.input 0 (by norm_num)) C.val mode accounting original.rule ν ≠ ⊤ →
        ∃ stopped : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting Seed,
          FirstFailureDomination (P.input 0 (by norm_num)) C.val mode accounting original stopped ∧
          ∃ (SimSeed : Type u) (ms : MeasurableSpace SimSeed),
            letI : MeasurableSpace SimSeed := ms
            ∃ (νs : Measure SimSeed), IsProbabilityMeasure νs ∧
              ∃ (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
                (data : OverlaySimulatorData P.sharedInstance Seed SimSeed),
                VirtualOverlayRepresentation P fee hfee C accounting ν νs stopped actual data ∧
                ∀ penalty : ℝ≥0∞,
                  paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule νs penalty ≤
                    expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting original.rule ν +
                      P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee +
                      penalty * risk (P.input 0 (by norm_num)) C.val mode accounting original.rule ν

end PDROC.OverlayDraft
