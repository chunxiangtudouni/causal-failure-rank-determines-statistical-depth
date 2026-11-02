module

public import PaperProofs.Paid.Claims
public import PaperProofs.Common.NativeRepairCount
public import PaperProofs.Common.NativeTestingKernel
public import PaperProofs.Common.NativeHistoryReplay

/-!
Exact surviving-entry and actual-payment obligations in paid-proofs:215--311.
Entering a stage alone is NOT survival: missed repairs may be followed by
legal advance and further spending. Actual eligibility reads the genuine
EARLY entry history and checks that all earlier writes were correct or
physically executed. A between-stage abandonment is assigned only to the
next required stage. The pending D08 claim factors this full eligibility
through the original seed and past world, without any future truth.

The original policy continues unchanged, including all failed-path charges.
Only an analytical marked decision is filled when a surviving stage never
writes; it is not an extra native write or an executed free correction.
All comparison policies and expectations remain the original full class.
The D08--D11 packages below are statements, not assumed Policy fields.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.Parameters

open Common Common.Native

universe u

/-- Everything here is an existing visible event, including the real
version-bound serial and actual execution. A commitment alone never resolves
a paid obligation. -/
def historyStageResolved (I : Instance) (history : List (VisibleEvent I)) (stage : I.Stage) : Bool :=
  match historyWrite history stage, historyReport history stage with
  | some (bit, serial), some (truth, reportSerial) =>
      (serial == reportSerial) && ((bit == truth) ||
        (historyExecutions history).any (fun execution =>
          (execution.1.stage == stage) && (execution.1.writeSerial == serial)))
  | _, _ => false

def healthyEntryHistory (I : Instance) (stage : I.Stage) (history : List (VisibleEvent I)) : Bool :=
  decide (∀ earlier : I.Stage, earlier.val < stage.val → historyStageResolved I history earlier = true)

def healthyEntryRecord (I : Instance) (stage : I.Stage) : EntryHistory I → Bool
  | none => false
  | some history => healthyEntryHistory I stage history

section Policy

variable {Seed : Type u} [MeasurableSpace Seed]

def actualSurvivingEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) :
    Set (Seed × (P.input fee hfee).World) :=
  {sample | healthyEntryRecord P.sharedInstance stage
    (entryHistory (P.input fee hfee) C.val mode accounting rule stage sample) = true}

theorem measurableSet_actualSurvivingEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    MeasurableSet (P.actualSurvivingEntry fee hfee C mode accounting rule stage) :=
  ((measurable_of_countable (healthyEntryRecord P.sharedInstance stage)).comp
    (measurable_entryHistory (P.input fee hfee) C.val mode accounting rule hm stage))
      (measurableSet_singleton true)

/-- A stop/abandonment after a resolved stage but before advance is assigned
to the NEXT required stage. Its unused potential fair bit is analysis-only;
the original run, observations and all payments are left untouched. -/
def nextStageFilledEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) :
    Set (Seed × (P.input fee hfee).World) :=
  {sample | ∃ n : ℕ,
    let state := run (P.input fee hfee) C.val mode accounting rule sample n
    state.halted = true ∧ state.cursor + 1 = stage.val ∧
      healthyEntryHistory P.sharedInstance stage state.history = true}

theorem measurableSet_nextStageFilledEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    MeasurableSet (P.nextStageFilledEntry fee hfee C mode accounting rule stage) := by
  have hn (n : ℕ) : MeasurableSet {sample : Seed × (P.input fee hfee).World |
      let state := run (P.input fee hfee) C.val mode accounting rule sample n
      state.halted = true ∧ state.cursor + 1 = stage.val ∧
        healthyEntryHistory P.sharedInstance stage state.history = true} :=
    (measurable_run (P.input fee hfee) C.val mode accounting rule hm n)
      (MeasurableSpace.measurableSet_top (s := {state : State P.sharedInstance |
        state.halted = true ∧ state.cursor + 1 = stage.val ∧
          healthyEntryHistory P.sharedInstance stage state.history = true}))
  have heq : P.nextStageFilledEntry fee hfee C mode accounting rule stage =
      ⋃ n : ℕ, {sample : Seed × (P.input fee hfee).World |
        let state := run (P.input fee hfee) C.val mode accounting rule sample n
        state.halted = true ∧ state.cursor + 1 = stage.val ∧
          healthyEntryHistory P.sharedInstance stage state.history = true} := by
    ext sample
    simp only [nextStageFilledEntry, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion hn

def survivingEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) :
    Set (Seed × (P.input fee hfee).World) :=
  P.actualSurvivingEntry fee hfee C mode accounting rule stage ∪
    P.nextStageFilledEntry fee hfee C mode accounting rule stage

theorem measurableSet_survivingEntry (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    MeasurableSet (P.survivingEntry fee hfee C mode accounting rule stage) :=
  (P.measurableSet_actualSurvivingEntry fee hfee C mode accounting rule hm stage).union
    (P.measurableSet_nextStageFilledEntry fee hfee C mode accounting rule hm stage)

/-- The actual ordinary bit, returning none when no write was made.
Analytical MAP filling is performed separately below. -/
noncomputable def actualOrdinaryDecision (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) : Option Bool := by
  classical
  exact if ∃ n : ℕ, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some true
    then some true else if ∃ n : ℕ,
      (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some false
    then some false else none

noncomputable def unwrittenSurvivingStages (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) :
    Finset P.sharedInstance.Stage := by
  classical
  exact Finset.univ.filter (fun stage => sample ∈ P.survivingEntry fee hfee C mode accounting rule stage ∧
    ¬ ∃ (n : ℕ) (bit : Bool), (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.written stage = some bit)

noncomputable def paidRunReviewCount (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) : ℕ∞ :=
  ⨆ n, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.reviews stage

/-- The genuine tape prefix at the actual total review count. Infinity is
handled BEFORE toNat: it has posterior-information cost phi(0)=infinity,
not the zero-observation prior. The finite zero case retains fair error 1/2. -/
noncomputable def paidRunPosteriorError (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) : ℝ :=
  let count := P.paidRunReviewCount fee hfee C mode accounting rule sample stage
  if count = 0 then 1 / 2 else if count = ⊤ then 0 else
    P.binarySymmetric.wordPosteriorError ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩

omit [MeasurableSpace Seed] in
theorem paidRunPosteriorError_infinite (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage)
    (hc : P.paidRunReviewCount fee hfee C mode accounting rule sample stage = ⊤) :
    P.paidRunPosteriorError fee hfee C mode accounting rule sample stage = 0 := by
  simp [paidRunPosteriorError, hc]

omit [MeasurableSpace Seed] in
theorem paidRunPosteriorError_zero (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage)
    (hc : P.paidRunReviewCount fee hfee C mode accounting rule sample stage = 0) :
    P.paidRunPosteriorError fee hfee C mode accounting rule sample stage = 1 / 2 := by
  simp [paidRunPosteriorError, hc]

/-- Preserve every actual non-MAP write. Fill an unmade finite-count
decision by the true posterior MAP rule (including the zero-count fair tie).
Infinite reviews have infinite observation cost; their arbitrary fill is
kept separate and never mistaken for a zero-count experiment. -/
noncomputable def filledOrdinaryDecision (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World)
    (stage : P.sharedInstance.Stage) : Bool :=
  match P.actualOrdinaryDecision fee hfee C mode accounting rule sample stage with
  | some bit => bit
  | none =>
      let count := P.paidRunReviewCount fee hfee C mode accounting rule sample stage
      if count = ⊤ then false else
        P.experiment.posteriorRecordDecision ((), ⟨count.toNat, fun k => (sample.2 stage).2 k.val⟩)

def markedErrorEvent (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (stage : P.sharedInstance.Stage) :
    Set (Seed × (P.input fee hfee).World) :=
  {sample | sample ∈ P.survivingEntry fee hfee C mode accounting rule stage ∧
    P.filledOrdinaryDecision fee hfee C mode accounting rule sample stage ≠ (sample.2 stage).1}

end Policy

/-- D08 includes all seed universes, actual before-birth independence, the
survival-mass bound, and the single possible analytical unwritten fill. -/
def SurvivingEntryClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        (∀ stage : P.sharedInstance.Stage,
          ∃ gate : Seed × (P.input fee hfee).PastWorld stage → Bool,
            Measurable gate ∧ ∀ sample,
              sample ∈ P.survivingEntry fee hfee C mode accounting policy.rule stage ↔
                gate ((P.input fee hfee).preBirthView stage sample) = true) ∧
        (∀ (sample : Seed × (P.input fee hfee).World) (stage : P.sharedInstance.Stage),
          sample ∈ P.nextStageFilledEntry fee hfee C mode accounting policy.rule stage →
            entryHistory (P.input fee hfee) C.val mode accounting policy.rule stage sample = none ∧
              P.paidRunReviewCount fee hfee C mode accounting policy.rule sample stage = 0) ∧
        (∀ sample, (P.unwrittenSurvivingStages fee hfee C mode accounting policy.rule sample).card ≤ 1) ∧
        (risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
          ∀ stage : P.sharedInstance.Stage,
            1 - P.targetRisk ≤ (P.input fee hfee).seededWorldLaw ν
              (P.survivingEntry fee hfee C mode accounting policy.rule stage))

/-- D09: all actual observations are charged, while only the surviving
pre-birth histories are retained on the information lower side. -/
def SurvivingInformationLower (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        ENNReal.ofReal P.a * (∑ stage : P.sharedInstance.Stage,
          ∫⁻ sample, (P.survivingEntry fee hfee C mode accounting policy.rule stage).indicator
            (fun sample => Statistics.BinarySymmetric.phi
              (P.paidRunPosteriorError fee hfee C mode accounting policy.rule sample stage)) sample
              ∂(P.input fee hfee).seededWorldLaw ν) ≤
          expectedObservationBill (P.input fee hfee) C.val mode accounting policy.rule ν

/-- D10's stronger pathwise target permits exactly one additional marked
error on a failing path. Actual R counts ALL executions, also after failure. -/
def MarkedFailureAllowance (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        (∀ sample,
          (∑ stage : P.sharedInstance.Stage,
            (P.markedErrorEvent fee hfee C mode accounting policy.rule stage).indicator
              (fun _ => (1 : ℝ≥0∞)) sample) ≤
            runRepairCount (P.input fee hfee) C.val mode accounting policy.rule sample +
              {sample | ¬ runSuccess (P.input fee hfee) C.val mode accounting policy.rule sample}.indicator
                (fun _ => (1 : ℝ≥0∞)) sample) ∧
        (risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
          (∑ stage : P.sharedInstance.Stage,
            (P.input fee hfee).seededWorldLaw ν (P.markedErrorEvent fee hfee C mode accounting policy.rule stage)) ≤
            expectedRepairCount (P.input fee hfee) C.val mode accounting policy.rule ν + P.targetRisk)

/-- This is an EXPECTATION comparison with the actual or filled decision,
not the false pointwise claim posterior error <= error indicator. -/
def MarkedPosteriorComparison (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        (∑ stage : P.sharedInstance.Stage,
          ∫⁻ sample, (P.survivingEntry fee hfee C mode accounting policy.rule stage).indicator
            (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hfee C mode accounting policy.rule sample stage)) sample
              ∂(P.input fee hfee).seededWorldLaw ν) ≤
          ∑ stage : P.sharedInstance.Stage,
            (P.input fee hfee).seededWorldLaw ν (P.markedErrorEvent fee hfee C mode accounting policy.rule stage)

def PosteriorFailureAllowance (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
          (∑ stage : P.sharedInstance.Stage,
            ∫⁻ sample, (P.survivingEntry fee hfee C mode accounting policy.rule stage).indicator
              (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hfee C mode accounting policy.rule sample stage)) sample
                ∂(P.input fee hfee).seededWorldLaw ν) ≤
            expectedRepairCount (P.input fee hfee) C.val mode accounting policy.rule ν + P.targetRisk

def OneFailureAllowance (P : PaperProofs.Paid.Parameters) : Prop :=
  P.MarkedPosteriorComparison.{u} ∧ P.MarkedFailureAllowance.{u} ∧ P.PosteriorFailureAllowance.{u}

noncomputable def survivalMassLower (P : PaperProofs.Paid.Parameters) : ℝ :=
  (P.certificate.stages : ℝ) * (1 - (P.certificate.risk : ℝ))

theorem survivalMassLower_pos (P : PaperProofs.Paid.Parameters) : 0 < P.survivalMassLower := by
  have hN : (0 : ℝ) < P.certificate.stages := by exact_mod_cast P.certificate.stages_pos
  have hd : (P.certificate.risk : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.risk_le
    norm_num at h
    exact h
  exact mul_pos hN (by linarith)

/-- D11 in extended expectations. The actual mean repair count is finite
by NativeRepairCount before conversion; no finite observation-cost hypothesis
is imposed, and the original same-risk comparator remains unrestricted. -/
def UsageLower (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
        risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
          let repairs := meanRepairCount (P.input fee hfee) C.val mode accounting policy.rule ν
          ENNReal.ofReal (P.a * P.survivalMassLower) *
              Statistics.BinarySymmetric.phi
                (min (1 / 2) ((repairs + (P.certificate.risk : ℝ)) / P.survivalMassLower)) +
            ENNReal.ofReal (fee : ℝ) * expectedRepairCount (P.input fee hfee) C.val mode accounting policy.rule ν ≤
              expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν

end PaperProofs.Paid.Parameters
