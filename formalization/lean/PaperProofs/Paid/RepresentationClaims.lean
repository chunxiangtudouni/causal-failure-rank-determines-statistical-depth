module

public import PaperProofs.Paid.PenaltyProgram
public import PaperProofs.Paid.Survival
public import PaperProofs.Paid.CalibratedBackend

/-!
Record-level existence comparisons of frozen paid-proofs.tex:120--169 and
349--398. These are statements about the original current-PAYMENT native
protocol, not current allocation with a later execution deadline.

No target below is a Policy field. All record simulators must produce legal
actual uncapped Native policies; genuine reports and handles alone authorize
physical corrections. Every fee is the supremum of actual prefix payments,
including payments before failure, abandonment, and nonreturn.

The conditional cells contain the ORIGINAL private seed, generated virtual
entry history, and auxiliary record. They exclude the simulator's additional
current-stage mixture/false-positive marks. Conditioning on the whole new
private seed would incorrectly reveal these fresh coins.

D27's actual rational/bit machine, peak-live-space semantics and rational-coin
sampler are not supplied here. Existing update labels are not a RAM model.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace PaperProofs.Paid

open Common Common.Native

universe u v

variable {I : Instance}

/-- First actual halted history. The none branch preserves nontermination;
it is not replaced by an empty successful or zero-fee trace. -/
noncomputable def completedHistory {Seed : Type u} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (sample : Seed × input.World) : EntryHistory I := by
  classical
  exact if h : ∃ n : ℕ, (run input C mode accounting rule sample n).halted = true
    then some (run input C mode accounting rule sample (Nat.find h)).history else none

theorem completedHistory_none_iff {Seed : Type u} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (sample : Seed × input.World) :
    completedHistory input C mode accounting rule sample = none ↔
      ¬ ∃ n : ℕ, (run input C mode accounting rule sample n).halted = true := by
  classical
  by_cases h : ∃ n : ℕ, (run input C mode accounting rule sample n).halted = true <;>
    simp [completedHistory, h]

theorem completedHistory_some_iff {Seed : Type u} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (sample : Seed × input.World) (history : List (VisibleEvent I)) :
    completedHistory input C mode accounting rule sample = some history ↔
      ∃ n : ℕ, (run input C mode accounting rule sample n).halted = true ∧
        (∀ k < n, (run input C mode accounting rule sample k).halted ≠ true) ∧
        (run input C mode accounting rule sample n).history = history := by
  classical
  constructor
  · intro hh
    by_cases he : ∃ n : ℕ, (run input C mode accounting rule sample n).halted = true
    · have hhistory : (run input C mode accounting rule sample (Nat.find he)).history = history := by
        simpa [completedHistory, he] using hh
      exact ⟨Nat.find he, Nat.find_spec he, fun _ hk => Nat.find_min he hk, hhistory⟩
    · simp [completedHistory, he] at hh
  · rintro ⟨n, hn, hbefore, hhistory⟩
    have he : ∃ k : ℕ, (run input C mode accounting rule sample k).halted = true := ⟨n, hn⟩
    have hfind : Nat.find he = n := (Nat.find_eq_iff he).mpr ⟨hn, hbefore⟩
    simp [completedHistory, he, hfind, hhistory]

theorem measurable_completedHistory {Seed : Type u} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hm : MeasurableRule rule) :
    Measurable (completedHistory input C mode accounting rule) := by
  have hhalt (n : ℕ) : MeasurableSet {sample : Seed × input.World |
      (run input C mode accounting rule sample n).halted = true} :=
    (measurable_run input C mode accounting rule hm n)
      (MeasurableSpace.measurableSet_top (s := {state : State I | state.halted = true}))
  apply measurable_to_countable'
  intro outcome
  cases outcome with
  | none =>
    have heq : (completedHistory input C mode accounting rule) ⁻¹' {none} =
        (⋃ n : ℕ, {sample : Seed × input.World |
          (run input C mode accounting rule sample n).halted = true})ᶜ := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, completedHistory_none_iff,
        Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
    rw [heq]
    exact (MeasurableSet.iUnion hhalt).compl
  | some history =>
    have hhistory (n : ℕ) : MeasurableSet {sample : Seed × input.World |
        (run input C mode accounting rule sample n).history = history} :=
      (measurable_run input C mode accounting rule hm n)
        (MeasurableSpace.measurableSet_top (s := {state : State I | state.history = history}))
    have heq : (completedHistory input C mode accounting rule) ⁻¹' {some history} =
        ⋃ n : ℕ, {sample : Seed × input.World |
            (run input C mode accounting rule sample n).halted = true} ∩
          ((⋂ k : ℕ, {sample : Seed × input.World |
            k < n → (run input C mode accounting rule sample k).halted ≠ true}) ∩
          {sample : Seed × input.World |
            (run input C mode accounting rule sample n).history = history}) := by
      ext sample
      simp only [Set.mem_preimage, Set.mem_singleton_iff, completedHistory_some_iff,
        Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    refine (hhalt n).inter ((MeasurableSet.iInter fun k => ?_).inter (hhistory n))
    by_cases hk : k < n
    · have hs : {sample : Seed × input.World |
          k < n → (run input C mode accounting rule sample k).halted ≠ true} =
          {sample : Seed × input.World |
            (run input C mode accounting rule sample k).halted = true}ᶜ := by
        ext sample
        simp [hk]
      rw [hs]
      exact (hhalt k).compl
    · simp [hk]

/-- Exact semantic permanence, independently of a proposed visible detector:
no finite continuation using REAL uncapped Steps can complete successfully. -/
def PermanentlyFailed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (world : input.World) (state : State I) : Prop :=
  ¬ ∃ final : State I,
    Relation.ReflTransGen (fun before after => ∃ action,
      Step input C .uncapped accounting (worldTapes input world) before action after) state final ∧
      final.halted = true ∧ final.ledger.success C

noncomputable def failureStop (state : State I) : State I :=
  if state.halted then state else stopState state true

/-- Data only. Theorems below must establish the stopping identity and every
risk/fee comparison; no permanence or performance is a Step premise. -/
def FirstFailureDomination {Seed : Type u} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (original : Policy input C mode accounting Seed)
    (stopped : Policy input C .uncapped accounting Seed) : Prop :=
  (∀ sample, runSuccess input C .uncapped accounting stopped.rule sample ↔
    runSuccess input C mode accounting original.rule sample) ∧
  (∀ sample n, (∀ k < n, ¬ PermanentlyFailed input C accounting sample.2
      (run input C mode accounting original.rule sample k)) →
    run input C .uncapped accounting stopped.rule sample n = run input C mode accounting original.rule sample n) ∧
  (∀ sample n, PermanentlyFailed input C accounting sample.2
      (run input C mode accounting original.rule sample n) →
    (∀ k < n, ¬ PermanentlyFailed input C accounting sample.2
      (run input C mode accounting original.rule sample k)) →
    ∀ extra, run input C .uncapped accounting stopped.rule sample (n + 1 + extra) =
      failureStop (run input C mode accounting original.rule sample n)) ∧
  ∀ sample, runObservationBill input C .uncapped accounting stopped.rule sample ≤
      runObservationBill input C mode accounting original.rule sample ∧
    runActualBill input C .uncapped accounting stopped.rule sample ≤
      runActualBill input C mode accounting original.rule sample

/-- The sampled old record excludes its later report. none denotes an old
abandonment/unmade decision; no physical native write is inserted for it. -/
structure AuxiliaryRecord where
  observations : List (Fin 2)
  decision : Option Bool
  deriving DecidableEq, Countable

instance : MeasurableSpace AuxiliaryRecord := ⊤
instance : MeasurableSingletonClass AuxiliaryRecord :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def AuxiliaryRecord.score (record : AuxiliaryRecord) : ℤ :=
  (record.observations.map (fun symbol => if symbol.val = 1 then (1 : ℤ) else -1)).sum

def AuxiliaryRecord.level (record : AuxiliaryRecord) : ℕ := record.score.natAbs

/-- Fixed tie orientation, as in the frozen representation proof. -/
def AuxiliaryRecord.orientation (record : AuxiliaryRecord) : Bool := decide (0 ≤ record.score)

/-- Source and auxiliary seed spaces remain arbitrary. These are merely
measurable-data candidates; correctness is a separate proposition below. -/
structure RecordSimulatorData (I : Instance) (SourceSeed : Type u) (SimSeed : Type v) where
  sourceSeed : SimSeed → SourceSeed
  shadow : SimSeed → List (VisibleEvent I) → List (VisibleEvent I)
  record : SimSeed → I.Stage → List (VisibleEvent I) → AuxiliaryRecord
  endpointCoin : SimSeed → I.Stage → Bool
  mixtureCoins : SimSeed → I.Stage → Bool × Bool
  falsePositiveCoin : SimSeed → I.Stage → Bool

def RecordSimulatorMeasurable {SourceSeed : Type u} {SimSeed : Type v}
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (data : RecordSimulatorData I SourceSeed SimSeed) : Prop :=
  Measurable data.sourceSeed ∧
    Measurable (fun pair : SimSeed × List (VisibleEvent I) => data.shadow pair.1 pair.2) ∧
    (∀ stage, Measurable (fun pair : SimSeed × List (VisibleEvent I) => data.record pair.1 stage pair.2)) ∧
    (∀ stage, Measurable (fun seed => data.endpointCoin seed stage)) ∧
    (∀ stage, Measurable (fun seed => data.mixtureCoins seed stage)) ∧
    ∀ stage, Measurable (fun seed => data.falsePositiveCoin seed stage)

inductive HistoryMark (I : Instance) where
  | writeError (stage : I.Stage) (error : Bool)
  | reserve (stage : I.Stage) (tool : I.Tool)
  | correction (stage : I.Stage) (tool : I.Tool)
  | advance (stage : I.Stage)
  | terminate (abandoned : Bool)
  deriving DecidableEq, Countable

/-- Error/correction/abandonment chronology, without review-clock padding or
version serials. The writing error is read only from its genuine report. -/
def markedHistory (history : List (VisibleEvent I)) : List (HistoryMark I) :=
  history.filterMap fun event => match event with
    | .report stage truth serial => match historyWrite history stage with
      | some (bit, writtenSerial) =>
        if writtenSerial = serial then some (.writeError stage (bit != truth)) else none
      | none => none
    | .committed handle tool => some (.reserve handle.stage tool)
    | .executed handle tool => some (.correction handle.stage tool)
    | .advanced stage => some (.advance stage)
    | .abandoned => some (.terminate true)
    | .stopped => some (.terminate false)
    | _ => none

def reportedWriteError (history : List (VisibleEvent I)) (stage : I.Stage) : Option Bool := do
  let written ← historyWrite history stage
  let reported ← historyReport history stage
  if written.2 = reported.2 then some (written.1 != reported.1) else none

def reservedPairs (history : List (VisibleEvent I)) : List (I.Stage × I.Tool) :=
  (historyCommitments history).map fun pair => (pair.1.stage, pair.2)

def executedPairs (history : List (VisibleEvent I)) : List (I.Stage × I.Tool) :=
  (historyExecutions history).map fun pair => (pair.1.stage, pair.2)

end PaperProofs.Paid

namespace PaperProofs.Paid.Parameters

open Common Common.Native Statistics.BinarySymmetric

universe u v

noncomputable def recordPosteriorError (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) : ℝ :=
  P.binarySymmetric.endpointError record.level

/-- Fill an abandonment decision by its MAP orientation only for analysis.
Every actual old non-MAP writing decision is retained. -/
noncomputable def recordDecisionError (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) : ℝ :=
  if record.decision.getD record.orientation = record.orientation then P.recordPosteriorError record
    else 1 - P.recordPosteriorError record

theorem recordPosteriorError_pos (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    0 < P.recordPosteriorError record := by
  change 0 < (P.binarySymmetric.endpointError record.level : ℝ)
  exact_mod_cast P.binarySymmetric.endpointError_pos record.level

theorem recordPosteriorError_le_half (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    P.recordPosteriorError record ≤ 1 / 2 := by
  change (P.binarySymmetric.endpointError record.level : ℝ) ≤ 1 / 2
  have h : (P.binarySymmetric.endpointError record.level : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) :=
    (Rat.cast_le (K := ℝ)).mpr (P.binarySymmetric.endpointError_le_half record.level)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

theorem recordDecisionError_bounds (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    P.recordPosteriorError record ≤ P.recordDecisionError record ∧
      P.recordDecisionError record ≤ 1 - P.recordPosteriorError record := by
  have hp := P.recordPosteriorError_le_half record
  unfold recordDecisionError
  split_ifs <;> constructor <;> linarith

/-- A separate finite-word mathematical obligation, not an assumed record
field: the actual posterior level is the magnitude of its signed score. -/
def AuxiliaryPosteriorLevels (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ record : AuxiliaryRecord,
    P.binarySymmetric.wordPosteriorError
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ = P.recordPosteriorError record

section Simulator

variable {SourceSeed : Type u} {SimSeed : Type v}

noncomputable def shadowCompletedHistory (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed)
    (sample : SimSeed × (P.input fee hfee).World) : EntryHistory P.sharedInstance :=
  (completedHistory (P.input fee hfee) C.val .uncapped accounting rule sample).map (data.shadow sample.1)

noncomputable def recordCell (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage)
    (record : AuxiliaryRecord) (B : Set (SourceSeed × List (VisibleEvent P.sharedInstance))) :
    Set (SimSeed × (P.input fee hfee).World) :=
  {sample | ∃ entry, entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry ∧
    (data.sourceSeed sample.1, data.shadow sample.1 entry) ∈ B ∧ data.record sample.1 stage entry = record}

noncomputable def stageObservationBill (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed) (stage : P.sharedInstance.Stage)
    (sample : SimSeed × (P.input fee hfee).World) : ℝ≥0∞ :=
  ENNReal.ofReal (P.reviewFee : ℝ) * (P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage : ℝ≥0∞)

noncomputable def actualWriteError (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed) (stage : P.sharedInstance.Stage)
    (sample : SimSeed × (P.input fee hfee).World) : Prop :=
  P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage =
    some (!((P.input fee hfee).truthAt sample.2 stage))

noncomputable def actualWriteErrorFlag (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed) (stage : P.sharedInstance.Stage)
    (sample : SimSeed × (P.input fee hfee).World) : Bool :=
  decide (P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage =
    some (!((P.input fee hfee).truthAt sample.2 stage)))

noncomputable def virtualWriteError (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) (stage : P.sharedInstance.Stage)
    (sample : SimSeed × (P.input fee hfee).World) : Prop :=
  ∃ n, reportedWriteError
    (data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history) stage = some true

def ShadowCausal (P : PaperProofs.Paid.Parameters)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  (∀ seed, data.shadow seed [] = []) ∧
    ∀ seed before after, before.IsPrefix after → (data.shadow seed before).IsPrefix (data.shadow seed after)

/-- Selected records reproduce the SOURCE local word/decision, not merely
an aggregate error probability. Virtual entry has not opened this fact. -/
def SourceRecordAlignment (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SimSeed] (ν : Measure SimSeed) (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
    ∀ history, completedHistory (P.input fee hfee) C.val .uncapped accounting rule sample = some history →
      ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
        historyCursor (data.shadow sample.1 entry) = stage.val ∧
        historyObservations (data.shadow sample.1 entry) stage = [] ∧
        historyWrite (data.shadow sample.1 entry) stage = none ∧
        (data.record sample.1 stage entry).observations.map Fin.val =
          historyObservations (data.shadow sample.1 history) stage ∧
        (data.record sample.1 stage entry).decision = historyWritten (data.shadow sample.1 history) stage

def SourceHistoryLaw (P : PaperProofs.Paid.Parameters)
    (sourceFee : ℚ) (hsource : 0 ≤ sourceFee) (actualFee : ℚ) (hactual : 0 ≤ actualFee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (sourceRule : PolicyRule P.sharedInstance SourceSeed) (actualRule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  Measurable (P.shadowCompletedHistory actualFee hactual C accounting actualRule data) ∧
    νactual.map data.sourceSeed = νsource ∧
    ((P.input actualFee hactual).seededWorldLaw νactual).map (fun sample =>
      (data.sourceSeed sample.1, P.shadowCompletedHistory actualFee hactual C accounting actualRule data sample)) =
    ((P.input sourceFee hsource).seededWorldLaw νsource).map (fun sample =>
      (sample.1, completedHistory (P.input sourceFee hsource) C.val .uncapped accounting sourceRule sample))

/-- This is an actual endpoint experiment on the current real tape. At level
zero rocEndpointTest supplies its zero-observation private guess. Abandonment
records may be copied immediately, deleting their nonnegative review work. -/
def BoundaryStageRealization (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SimSeed] (ν : Measure SimSeed) (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
    ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
      let record := data.record sample.1 stage entry
      match record.decision with
      | none => P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage = none ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = 0
      | some decision =>
        let test := P.binarySymmetric.rocEndpointTest record.level
        let tape := (P.input fee hfee).reviewAt sample.2 stage
        ∃ n : ℕ, test.rule.stop (data.endpointCoin sample.1 stage) tape = (n : ℕ∞) ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = (n : ℕ∞) ∧
          P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage =
            some (Bool.xor decision (Bool.xor record.orientation (test.rule.decision (data.endpointCoin sample.1 stage) tape)))

/-- For every measurable generated virtual-history event and writing record,
the posterior and mean charge are exact. No singleton-seed conditioning or
regular conditional probability hypothesis is used. -/
def BoundaryRecordCells (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed] (ν : Measure SimSeed)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ stage record decision, record.decision = some decision →
    ∀ B : Set (SourceSeed × List (VisibleEvent P.sharedInstance)), MeasurableSet B →
      let μ := (P.input fee hfee).seededWorldLaw ν
      let cell := P.recordCell fee hfee C accounting rule data stage record B
      MeasurableSet cell ∧
      (∫⁻ sample, cell.indicator (P.stageObservationBill fee hfee C accounting rule stage) sample ∂μ) =
        ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) * μ cell ∧
      μ (cell ∩ {sample | P.actualWriteError fee hfee C accounting rule stage sample}) =
        ENNReal.ofReal (P.recordDecisionError record) * μ cell ∧
      μ (cell ∩ {sample | ∃ history,
        P.shadowCompletedHistory fee hfee C accounting rule data sample = some history ∧
        (historyReport history stage).map Prod.fst = some (!record.orientation)}) =
        ENNReal.ofReal (P.recordPosteriorError record) * μ cell

def BoundaryRepresentation (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  RecordSimulatorMeasurable data ∧ P.ShadowCausal data ∧
    P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data ∧
    P.SourceHistoryLaw fee hfee fee hfee C accounting νsource νactual source.rule actual.rule data ∧
    P.BoundaryStageRealization fee hfee C accounting νactual actual.rule data ∧
    P.BoundaryRecordCells fee hfee C accounting νactual actual.rule data ∧
    (P.input fee hfee).seededWorldLaw νsource
      {sample | completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample = none} = 0 ∧
    (P.input fee hfee).seededWorldLaw νactual
      {sample | completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0 ∧
    (∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw νactual,
      (completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample).map markedHistory =
        (P.shadowCompletedHistory fee hfee C accounting actual.rule data sample).map markedHistory) ∧
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting actual.rule νactual ≤
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule νsource ∧
    P.actualCorrectionBillLaw fee hfee C .uncapped accounting actual.rule νactual =
      P.actualCorrectionBillLaw fee hfee C .uncapped accounting source.rule νsource ∧
    risk (P.input fee hfee) C.val .uncapped accounting actual.rule νactual =
      risk (P.input fee hfee) C.val .uncapped accounting source.rule νsource

end Simulator

/-- Full D06 target. The original finite-cost hypothesis is on the full
actual expected bill; no finite-ET/MAP condition narrows a policy infimum.
The final objective comparison retains infinite penalties and failure fees. -/
def RecordRepresentationClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.AuxiliaryPosteriorLevels ∧
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
      letI : IsProbabilityMeasure ν := hν
      ∀ original : Policy (P.input fee hfee) C.val mode accounting Seed,
        expectedBill (P.input fee hfee) C.val mode accounting original.rule ν ≠ ⊤ →
        ∃ stopped : Policy (P.input fee hfee) C.val .uncapped accounting Seed,
          FirstFailureDomination (P.input fee hfee) C.val mode accounting original stopped ∧
          ∃ (SimSeed : Type u) (ms : MeasurableSpace SimSeed),
            letI : MeasurableSpace SimSeed := ms
            ∃ (νs : Measure SimSeed), IsProbabilityMeasure νs ∧
              ∃ (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
                (data : RecordSimulatorData P.sharedInstance Seed SimSeed),
                P.BoundaryRepresentation fee hfee C accounting ν νs stopped actual data ∧
                ∀ penalty : ℝ≥0∞,
                  paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule νs penalty ≤
                    expectedBill (P.input fee hfee) C.val mode accounting original.rule ν +
                      penalty * risk (P.input fee hfee) C.val mode accounting original.rule ν

/-- D14's exact false-positive probability, without any positive-fee or
MAP restriction on the old decision error e. -/
noncomputable def falsePositiveProbability (e p : ℝ) : ℝ := (e - p) / (1 - p)

theorem falsePositiveProbability_mem_Icc (e p : ℝ) (_hp : 0 ≤ p) (hpone : p < 1)
    (hpe : p ≤ e) (he : e ≤ 1) : falsePositiveProbability e p ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 0 < 1 - p := sub_pos.mpr hpone
  constructor
  · exact div_nonneg (sub_nonneg.mpr hpe) hd.le
  · unfold falsePositiveProbability
    exact (div_le_one hd).mpr (by linarith)

theorem falsePositiveProbability_mix (e p : ℝ) (hpone : p < 1) :
    p + (1 - p) * falsePositiveProbability e p = e := by
  unfold falsePositiveProbability
  field_simp [(sub_pos.mpr hpone).ne']; ring

def coupledVirtualError (actualError freshMark : Bool) : Bool := actualError || freshMark

theorem actualError_le_coupledVirtualError (actualError freshMark : Bool) :
    actualError = true → coupledVirtualError actualError freshMark = true := by
  intro h
  simp [coupledVirtualError, h]

noncomputable def overlayRecordTarget (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (record : AuxiliaryRecord) : ℝ :=
  min (P.recordPosteriorError record) (P.overlayError fee)

theorem overlayRecordTarget_pos (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : 0 < P.overlayRecordTarget fee record :=
  lt_min (P.recordPosteriorError_pos record) (P.overlayError_pos fee hfee)

theorem overlayRecordTarget_le_half (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (record : AuxiliaryRecord) : P.overlayRecordTarget fee record ≤ 1 / 2 :=
  (min_le_left _ _).trans (P.recordPosteriorError_le_half record)

theorem overlayRecordTarget_le_decisionError (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (record : AuxiliaryRecord) : P.overlayRecordTarget fee record ≤ P.recordDecisionError record :=
  (min_le_left _ _).trans (P.recordDecisionError_bounds record).1

theorem overlayRecord_falsePositive_mem_Icc (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (hfee : 0 ≤ fee) (record : AuxiliaryRecord) :
    falsePositiveProbability (P.recordDecisionError record) (P.overlayRecordTarget fee record) ∈ Set.Icc (0 : ℝ) 1 := by
  apply falsePositiveProbability_mem_Icc
  · exact (P.overlayRecordTarget_pos fee hfee record).le
  · linarith [P.overlayRecordTarget_le_half fee record]
  · exact P.overlayRecordTarget_le_decisionError fee record
  · have h := (P.recordDecisionError_bounds record).2
    linarith [P.recordPosteriorError_pos record]

/-- The exact actual MAP experiment prescribed in D14, implemented by the
existing two-adjacent-endpoint initial mixture, including its fair m0 bit.
Its performance remains an obligation, not an AdmissibleRule field. -/
noncomputable def overlayRecordTest (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : P.binarySymmetric.experiment.AdmissibleRule (Bool × Bool) :=
  P.binarySymmetric.adjacentMixtureTest
    (P.binarySymmetric.rocIndex (P.overlayRecordTarget fee record) (P.overlayRecordTarget_pos fee hfee record))

section Overlay

variable {SourceSeed : Type u} {SimSeed : Type v}

/-- Each writing record executes the concrete MAP mixture on the actual
current tape. Abandonment records perform no write and no extra reviews.
Finite stopping is a conclusion in this witness, never an input restriction. -/
def OverlayStageRealization (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SimSeed] (ν : Measure SimSeed) (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ᵐ sample ∂(P.input fee hfee).seededWorldLaw ν,
    ∀ stage entry, entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
      let record := data.record sample.1 stage entry
      match record.decision with
      | none => P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage = none ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = 0
      | some _ =>
        let test := P.overlayRecordTest fee hfee record
        let tape := (P.input fee hfee).reviewAt sample.2 stage
        ∃ n : ℕ, test.rule.stop (data.mixtureCoins sample.1 stage) tape = (n : ℕ∞) ∧
          P.paidRunReviewCount fee hfee C .uncapped accounting rule sample stage = (n : ℕ∞) ∧
          P.actualOrdinaryDecision fee hfee C .uncapped accounting rule sample stage =
            some (test.rule.decision (data.mixtureCoins sample.1 stage) tape) ∧
          (if test.rule.decision (data.mixtureCoins sample.1 stage) tape then
            0 ≤ P.binarySymmetric.experiment.logOddsScore tape n
           else P.binarySymmetric.experiment.logOddsScore tape n ≤ 0)

/-- Genuine all-prefix physical calls use a subset of virtual reserved rights
and virtual corrected stage-tool pairs. Even on a failing path, a virtual
report alone never supplies a handle to Native.Step. Actual errors are
dominated on EVERY path. The exact false-positive equation applies only
after a real report; an unreturned test never activates a pre-drawn mark,
and no virtual report may precede its real report. -/
def OverlayPathCoupling (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  (∀ sample n,
    let actual := (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history
    let virtual := data.shadow sample.1 actual
    (reservedPairs actual).Sublist (reservedPairs virtual) ∧
    (executedPairs actual).Sublist (executedPairs virtual) ∧
    historyUsed actual ⊆ historyUsed virtual) ∧
  (∀ sample stage, P.actualWriteError fee hfee C accounting rule stage sample →
    P.virtualWriteError fee hfee C accounting rule data stage sample) ∧
  (∀ sample stage entry decision,
    entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
    (data.record sample.1 stage entry).decision = some decision →
    (∃ n, (historyReport
      (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history stage).isSome = true) →
      (P.virtualWriteError fee hfee C accounting rule data stage sample ↔
        P.actualWriteError fee hfee C accounting rule stage sample ∨ data.falsePositiveCoin sample.1 stage = true)) ∧
  (∀ sample n stage,
    let actual := (run (P.input fee hfee) C.val .uncapped accounting rule sample n).history
    let virtual := data.shadow sample.1 actual
    (historyReport virtual stage).isSome = true →
      (historyReport actual stage).isSome = true ∧
      ∀ entry decision,
        entryHistory (P.input fee hfee) C.val .uncapped accounting rule stage sample = some entry →
        (data.record sample.1 stage entry).decision = some decision →
        (historyReport virtual stage).map Prod.fst = some (Bool.xor decision
          (P.actualWriteErrorFlag fee hfee C accounting rule stage sample || data.falsePositiveCoin sample.1 stage))) ∧
  ∀ sample n,
    (run (P.input fee hfee) C.val .uncapped accounting rule sample n).ledger.executions.length ≤
      min P.certificate.stages P.tools

/-- All measurable old-seed/virtual-entry gates are allowed. Current fresh
mixing and false-positive marks remain integrated, so these are exactly
conditional-on-record identities and not a false full-new-seed conditioning.
All mean charges are ENNReal; there is no toReal of an infinite expectation. -/
def OverlayRecordCells (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed] (ν : Measure SimSeed)
    (rule : PolicyRule P.sharedInstance SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  ∀ stage record decision, record.decision = some decision →
    ∀ B : Set (SourceSeed × List (VisibleEvent P.sharedInstance)), MeasurableSet B →
      let μ := (P.input fee hfee).seededWorldLaw ν
      let cell := P.recordCell fee hfee C accounting rule data stage record B
      let p := P.overlayRecordTarget fee record
      let e := P.recordDecisionError record
      let actualError := {sample | P.actualWriteError fee hfee C accounting rule stage sample}
      let virtualError := {sample | P.virtualWriteError fee hfee C accounting rule data stage sample}
      MeasurableSet cell ∧ MeasurableSet actualError ∧ MeasurableSet virtualError ∧
      μ (cell ∩ actualError) = ENNReal.ofReal p * μ cell ∧
      μ (cell ∩ virtualError) = ENNReal.ofReal e * μ cell ∧
      μ ((cell ∩ actualErrorᶜ) ∩ virtualError) =
        ENNReal.ofReal (falsePositiveProbability e p) * μ (cell ∩ actualErrorᶜ) ∧
      (∫⁻ sample, cell.indicator (P.stageObservationBill fee hfee C accounting rule stage) sample ∂μ) =
        P.binarySymmetric.rocPrice p * μ cell

/-- The all-path bill upper amounts prior to D13's scalar estimates. -/
noncomputable def overlayObservationIncrement (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ≥0∞ :=
  (P.certificate.stages : ℝ≥0∞) * P.binarySymmetric.rocPrice (P.overlayError fee)

noncomputable def overlayCorrectionAmount (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℝ≥0∞ :=
  (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal ((fee : ℝ) * P.overlayError fee)

def VirtualOverlayRepresentation (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    [MeasurableSpace SourceSeed] [MeasurableSpace SimSeed]
    (νsource : Measure SourceSeed) (νactual : Measure SimSeed)
    (source : Policy (P.input 0 (by norm_num)) C.val .uncapped accounting SourceSeed)
    (actual : Policy (P.input fee hfee) C.val .uncapped accounting SimSeed)
    (data : RecordSimulatorData P.sharedInstance SourceSeed SimSeed) : Prop :=
  RecordSimulatorMeasurable data ∧ P.ShadowCausal data ∧
    P.SourceRecordAlignment fee hfee C accounting νactual actual.rule data ∧
    P.SourceHistoryLaw 0 (by norm_num) fee hfee C accounting νsource νactual source.rule actual.rule data ∧
    P.OverlayStageRealization fee hfee C accounting νactual actual.rule data ∧
    P.OverlayPathCoupling fee hfee C accounting actual.rule data ∧
    P.OverlayRecordCells fee hfee C accounting νactual actual.rule data ∧
    (P.input fee hfee).seededWorldLaw νactual
      {sample | completedHistory (P.input fee hfee) C.val .uncapped accounting actual.rule sample = none} = 0 ∧
    (∀ sample n,
      let virtual := data.shadow sample.1 (run (P.input fee hfee) C.val .uncapped accounting actual.rule sample n).history
      (.stopped ∈ virtual ∧ ∀ stage, historyStageResolved P.sharedInstance virtual stage = true) →
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

/-- Full D14 target, independent of the numerical proof D13. Every finite-cost
original free full-history policy is included, with arbitrary private-seed
universe, non-MAP decisions and failed-path spending. The SAME current-payment
contract, accounting and risk are used; only the output's caps are relaxed.
No H0 or numeric certificate is added to the supplied policy. -/
def VirtualErrorCouplingClaims (P : PaperProofs.Paid.Parameters) : Prop :=
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
                (data : RecordSimulatorData P.sharedInstance Seed SimSeed),
                P.VirtualOverlayRepresentation fee hfee C accounting ν νs stopped actual data ∧
                ∀ penalty : ℝ≥0∞,
                  paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule νs penalty ≤
                    expectedObservationBill (P.input 0 (by norm_num)) C.val mode accounting original.rule ν +
                      P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee +
                      penalty * risk (P.input 0 (by norm_num)) C.val mode accounting original.rule ν

@[simp] theorem overlayObservationIncrement_zero (P : PaperProofs.Paid.Parameters) :
    P.overlayObservationIncrement 0 = 0 := by
  rw [overlayObservationIncrement, P.overlayError_zero_rocPrice, mul_zero]

@[simp] theorem overlayCorrectionAmount_zero (P : PaperProofs.Paid.Parameters) :
    P.overlayCorrectionAmount 0 = 0 := by
  simp [overlayCorrectionAmount]

/-- Infimum over ACTUAL legal uncapped boundary-record policies. Its extra
qualification is only the explicit local endpoint/flip script, with measurable
record selection before the fresh tape. It contains no risk, mean-cost or
optimality conclusion; those are not smuggled into the comparison class. -/
noncomputable def symmetricRecordPenaltyValue (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (penalty : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (Seed : Type u), ⨅ (m : MeasurableSpace Seed),
    letI : MeasurableSpace Seed := m
    ⨅ (ν : Measure Seed) (_hν : IsProbabilityMeasure ν),
      ⨅ (actual : Policy (P.input fee hfee) C.val .uncapped accounting Seed),
        ⨅ (data : RecordSimulatorData P.sharedInstance Unit Seed)
          (_hm : RecordSimulatorMeasurable data)
          (_hshape : P.BoundaryStageRealization fee hfee C accounting ν actual.rule data),
          paidPenaltyObjective (P.input fee hfee) C.val accounting actual.rule ν penalty

/-- The unrestricted full-policy infimum is below the structural subclass
infimum. This direction needs neither D06 nor an information/ROC premise. -/
theorem paidPenaltyValue_le_symmetricRecordPenaltyValue (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (penalty : ℝ≥0∞) :
    paidPenaltyValue (P.input fee hfee) C.val accounting penalty ≤
      P.symmetricRecordPenaltyValue.{u} fee hfee C accounting penalty := by
  unfold symmetricRecordPenaltyValue
  refine le_iInf fun Seed => le_iInf fun m => ?_
  let : MeasurableSpace Seed := m
  refine le_iInf fun ν => le_iInf fun hν => ?_
  let : IsProbabilityMeasure ν := hν
  refine le_iInf fun actual => le_iInf fun _data => le_iInf fun _hm => le_iInf fun _hshape => ?_
  exact paidPenaltyValue_le_policy_any_seed (P.input fee hfee) C.val accounting penalty actual ν

/-- The infimum claim is separate from every full comparator: no finite-cost
or MAP qualifier is imposed on paidPenaltyValue. All penalties, including
infinity, use the original actual bill and failure probability. -/
def RepresentationAtPenaltyInfima (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (penalty : ℝ≥0∞),
    P.symmetricRecordPenaltyValue.{u} fee hfee C accounting penalty =
      paidPenaltyValue (P.input fee hfee) C.val accounting penalty

def FirstFailureRepresentationClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.RecordRepresentationClaims.{u} ∧ P.RepresentationAtPenaltyInfima.{u}

end PaperProofs.Paid.Parameters
