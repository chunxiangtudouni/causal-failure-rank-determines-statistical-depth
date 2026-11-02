module

public import PaperProofs.Star.LatePosterior
public import PaperProofs.Common.ReferenceController
public import PaperProofs.Statistics.ControllerThresholds
public import PaperProofs.Statistics.BSCStoppedPosterior
public import PaperProofs.Retained.NativeMatching

/-!
First-round C07--C12 statements for the UNIQUE frozen star-proofs.tex.
The fixed rules below name the actual first-bit/count/terminal-matching
scripts, rather than an arbitrary family whose H0 could shrink qualification.
All performance, legality, asymptotics and implementation claims are separate
Prop targets; none is a Policy field or an axiom. Native.value remains the
original full randomized visible-history infimum. Real delta and its EXACT
reference budget delta/2 are retained; no rational approximation is substituted.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Star

open Common Common.Native Statistics

inductive PortKind where
  | current
  | earlyRetained
  | lateRetained
  deriving DecidableEq

def PortKind.contracts (kind : PortKind) {I : Instance} (C : Contract I) : Prop :=
  match kind with
  | .current => C.IsCurrentAllocation
  | .earlyRetained => C.IsEarlyRetained
  | .lateRetained => C.IsLateRetained

/-- The actual real-target first exit. The inclusive n=0 boundary is kept.
This is not defined through error, expected cost or a numerical recurrence. -/
noncomputable def realPosteriorStop (E : Statistics.BinaryExperiment) (p : ℝ) (tape : E.Tape) : ℕ∞ :=
  sInf {t : ℕ∞ | ∃ n : ℕ, t = n ∧ Real.log ((1 - p) / p) ≤ |E.logOddsScore tape n|}

namespace Parameters

universe u

def firstTool (P : Star.Parameters) : Fin P.tools := ⟨0, by have h := P.tools_ge_two; omega⟩

/-- Exactly p_j(r), extending the existing rational/analytic threshold API
to the real risk parameter in the original proposition. -/
noncomputable def starTargetReal (r : ℝ) (j : ℕ) : ℝ :=
  1 / (4 * (1 + (analyticControllerB (1 / r) j : ℝ)))

noncomputable def countTargetReal (r : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then r else starTargetReal r k

def countTargetRat (r : ℚ) (k : ℕ) : ℚ := if k = 0 then r else controllerTarget r k

noncomputable def countBudgetReal (P : Star.Parameters) (r : ℝ) : ℕ → ℝ
  | 0 => r
  | j + 1 => min (1 / 4) (P.countBudgetReal r j / countTargetReal (P.countBudgetReal r j) (P.tools - j))

def countBudgetRat (P : Star.Parameters) (r : ℚ) : ℕ → ℚ
  | 0 => r
  | j + 1 => min (1 / 4) (P.countBudgetRat r j / countTargetRat (P.countBudgetRat r j) (P.tools - j))

def reportedError {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : Bool :=
  match historyWritten history stage, historyReport history stage with
  | some bit, some (truth, _) => bit != truth
  | _, _ => false

def reportedCorrect {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : Bool :=
  match historyWritten history stage, historyReport history stage with
  | some bit, some (truth, _) => bit == truth
  | _, _ => false

def previousAllErrors {I : Instance} (history : List (VisibleEvent I)) (stage : I.Stage) : Bool :=
  (List.ofFn (fun i : I.Stage => !(decide (i.val < stage.val)) || reportedError history i)).all id

noncomputable def chosenTargetReal (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) : Option ℝ :=
  match kind, order with
  | .lateRetained, _ => if stage.val = 0 then some r else none
  | .current, .universalFirst =>
    match stageLabel P.tools .universalFirst stage with
    | none => some (starTargetReal r 1)
    | some tool => if tool.val = 0 && reportedError history (universalStage P.tools .universalFirst)
        then some (min (1 / 4) (r / starTargetReal r 1)) else none
  | _, _ => if previousAllErrors history stage then
      some (countTargetReal (P.countBudgetReal r stage.val) (P.tools - stage.val)) else none

def chosenTargetRat (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℚ)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) : Option ℚ :=
  match kind, order with
  | .lateRetained, _ => if stage.val = 0 then some r else none
  | .current, .universalFirst =>
    match stageLabel P.tools .universalFirst stage with
    | none => some (controllerTarget r 1)
    | some tool => if tool.val = 0 && reportedError history (universalStage P.tools .universalFirst)
        then some (min (1 / 4) (r / controllerTarget r 1)) else none
  | _, _ => if previousAllErrors history stage then
      some (countTargetRat (P.countBudgetRat r stage.val) (P.tools - stage.val)) else none

def firstOfFinset {n : ℕ} (items : Finset (Fin n)) : Option (Fin n) :=
  if h : items.Nonempty then some (items.min' h) else none

def currentToolChoice (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    Option (starInstance P.tools order).Tool :=
  match stageLabel P.tools order stage with
  | some tool => if (historyCommitments history).any (fun pair => pair.2.val == tool.val) then none else some tool
  | none => match order with
    | .universalFirst => if (historyCommitments history).any (fun pair => pair.2.val == 0) then none else some P.firstTool
    | .singletonsFirst => firstOfFinset (Finset.univ.filter fun tool : Fin P.tools =>
        !(historyCommitments history).any (fun pair => pair.2.val == tool.val))

/-- The explicit star matching from C:9--13: wrong singletons use their own
tool; an erroneous universal uses the first correctly written singleton. -/
def retainedToolChoice (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage) :
    Option (starInstance P.tools order).Tool :=
  match stageLabel P.tools order stage with
  | some tool => some tool
  | none => firstOfFinset (Finset.univ.filter fun tool => reportedCorrect history (singletonStage P.tools order tool))

def repairAction (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) (stage : (starInstance P.tools order).Stage)
    (tool : Option (starInstance P.tools order).Tool) (done : Action (starInstance P.tools order)) :
    Action (starInstance P.tools order) :=
  if (historyExecutions history).any (fun pair => pair.1.stage == stage) then done else
  match (historyCommitments history).find? (fun pair => pair.1.stage == stage) with
  | some pair => .execute pair.1 pair.2
  | none => match referenceVisibleHandle history stage, tool with
    | some handle, some chosen => .allocate handle chosen
    | _, _ => .abandon

def barrierAction (P : Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order))) : Action (starInstance P.tools order) :=
  let errors := Finset.univ.filter fun i => reportedError history i
  if P.tools < errors.card then .abandon else
  let pending := errors.filter fun i => !(historyExecutions history).any (fun pair => pair.1.stage == i)
  match firstOfFinset pending with
  | none => .stop
  | some stage => P.repairAction order history stage (P.retainedToolChoice order history stage) .stop

def candidateWithTesting (P : Star.Parameters) (order : Order) (kind : PortKind)
    (testing : List (VisibleEvent (starInstance P.tools order)) → (starInstance P.tools order).Stage →
      Action (starInstance P.tools order))
    (history : List (VisibleEvent (starInstance P.tools order))) : Action (starInstance P.tools order) :=
  if historyHalted history then .stop else
  if hstage : historyCursor history < (starInstance P.tools order).stageCount then
    let stage : (starInstance P.tools order).Stage := ⟨historyCursor history, hstage⟩
    match historyWritten history stage with
    | none => testing history stage
    | some _ => match kind with
      | .current => match historyReport history stage with
        | none => .abandon
        | some _ => if reportedError history stage then
            P.repairAction order history stage (P.currentToolChoice order history stage) (.advance stage)
          else .advance stage
      | .earlyRetained | .lateRetained => .advance stage
  else if historyCursor history = (starInstance P.tools order).stageCount then
    match kind with
    | .current => .stop
    | .earlyRetained | .lateRetained => P.barrierAction order history
  else .abandon

noncomputable def testingActionReal (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) : Action (starInstance P.tools order) := by
  classical
  exact match P.chosenTargetReal order kind r history stage with
  | none => .write stage false
  | some target =>
    if hv : ∀ symbol ∈ historyObservations history stage, symbol < P.channel.experiment.alphabetSize then
      let word := historyObservationWord (P.input order) history stage hv
      if Real.log ((1 - target) / target) ≤ |P.channel.experiment.stoppedWordScore word| then
        .write stage (decide (0 ≤ P.channel.experiment.stoppedWordScore word))
      else match limit with
        | none => .review stage
        | some quota => if (historyObservations history stage).length < quota then .review stage else .abandon
    else .abandon

def testingActionRat (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℚ)
    (limit : Option ℕ) (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) : Action (starInstance P.tools order) :=
  match P.chosenTargetRat order kind r history stage with
  | none => .write stage false
  | some target =>
    if hv : ∀ symbol ∈ historyObservations history stage, symbol < P.channel.experiment.alphabetSize then
      let word := historyObservationWord (P.input order) history stage hv
      if P.channel.experiment.rationalWordHits target word then .write stage (P.channel.experiment.rationalWordMAP word)
      else match limit with
        | none => .review stage
        | some quota => if (historyObservations history stage).length < quota then .review stage else .abandon
    else .abandon

noncomputable def starReferenceRule (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) {Seed : Type*} : PolicyRule (starInstance P.tools order) Seed :=
  fun _ history => P.candidateWithTesting order kind (P.testingActionReal order kind r limit) history

/-- An explicitly rational/integer algorithm, with no log/KL oracle. Its
agreement with the real-target reference is an independent target below. -/
def starRationalRule (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℚ)
    (limit : Option ℕ) {Seed : Type*} : PolicyRule (starInstance P.tools order) Seed :=
  fun _ history => P.candidateWithTesting order kind (P.testingActionRat order kind r limit) history

theorem measurable_starReferenceRule (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) {Seed : Type*} [MeasurableSpace Seed] :
    MeasurableRule (P.starReferenceRule order kind r limit (Seed := Seed)) :=
  (measurable_of_countable (P.candidateWithTesting order kind (P.testingActionReal order kind r limit))).comp measurable_snd

noncomputable def countObservationEnvelope (P : Star.Parameters) : ℕ → ℝ → ℝ
  | 0, r => P.channel.a * (Real.log (1 / r) + P.channel.h)
  | k + 1, r =>
    P.channel.a * (Real.log (1 / starTargetReal r (k + 1)) + P.channel.h) +
      starTargetReal r (k + 1) * P.countObservationEnvelope k (min (1 / 4) (r / starTargetReal r (k + 1)))

noncomputable def currentObservationEnvelope (P : Star.Parameters) (r : ℝ) : ℝ :=
  P.channel.a * (Real.log (1 / starTargetReal r 1) + P.channel.h) + starTargetReal r 1 *
    P.channel.a * (Real.log (1 / min (1 / 4) (r / starTargetReal r 1)) + P.channel.h)

def priceDepth (P : Star.Parameters) (order : Order) (kind : PortKind) : ℕ :=
  match kind, order with
  | .lateRetained, _ => 1
  | .current, .universalFirst => 2
  | _, _ => P.tools + 1

noncomputable def leadingScale (P : Star.Parameters) (order : Order) (kind : PortKind) (delta : ℝ) : ℝ :=
  P.channel.a * iteratedLog (P.priceDepth order kind) delta⁻¹

def commonExponentRat (P : Star.Parameters) (delta : ℚ) : ℕ :=
  max 1 (Nat.clog 2 ⌈20 * (P.tools + 1 : ℕ) / delta⌉₊)

def commonQuota (P : Star.Parameters) (exponent : ℕ) : ℕ :=
  Nat.ceil (2 * (exponent : ℚ) / P.channel.gamma ^ 2)

/-- Only original numerical resources and this FIXED script's actual H0.
No policy risk, monetary bound, finite ET or price conclusion is assumed.
Legality/native-policy existence remains a construction conclusion. -/
structure OriginalStarQualification (P : Star.Parameters) (order : Order) (kind : PortKind)
    (delta : ℝ) (exponent : ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : Prop where
  minimal_exponent : IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent
  stage_quota : ∀ i, P.commonQuota exponent ≤ C.reviewQuota i
  total_calls : C.normalCallBound + (P.tools + 1) * P.commonQuota exponent + P.tools ≤ C.totalCallCap
  normal_calls : ∀ sample n,
    (run (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)) (Seed := Unit)) sample n).ledger.normalCalls ≤
        (C.normalCallBound : ℕ∞)

def ReferenceLegality (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∃ policy : Policy (P.input order) C .uncapped accounting Unit,
    policy.rule = P.starReferenceRule order kind r limit

/-- All already-executed corrections, also on failures, retain their fee.
Commitments do not enter this actual bill. -/
def ReferenceAllPathCharges (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∀ sample : Unit × (P.input order).World,
    (∀ n, (run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit)
      sample n).ledger.executions.length ≤ P.tools) ∧
    runActualBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit) sample ≤
      runObservationBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit) sample +
        (P.tools : ℝ≥0∞) * ENNReal.ofReal (P.correctionFee : ℝ)

def ImmediateExecution (P : Star.Parameters) (order : Order) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∀ (sample : Unit × (P.input order).World) n stage,
    let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit) sample n
    P.starReferenceRule order .current r limit () s.history = .advance stage →
    s.ledger.written stage = some (!s.ledger.truth stage) →
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage ∧ e.atTime < s.clock

def CurrentToolIdentities (P : Star.Parameters) (order : Order) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∀ (sample : Unit × (P.input order).World) n e,
    e ∈ (run (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit) sample n).ledger.executions →
      match stageLabel P.tools order e.handle.stage with
      | some tool => e.tool.val = tool.val
      | none => order = .universalFirst → e.tool.val = 0

def RetainedNoEarlyCommitment (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∀ (sample : Unit × (P.input order).World) n,
    let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit) sample n
    ¬ allWritten s.ledger → s.ledger.commitments = [] ∧ s.ledger.executions = []

/-- A.e. completion is a construction target, never a comparator condition.
Retained all-error failures make no physical correction; current failures
retain all singleton corrections already executed inside their windows. -/
def TerminalCriterion (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order)) : Prop :=
  ∀ᵐ sample ∂((P.input order).seededWorldLaw (Measure.dirac ())), ∃ n,
    let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n
    s.halted = true ∧ allWritten s.ledger ∧
      (s.ledger.success C ↔ (Retained.ordinaryMismatches s.ledger).card ≤ P.tools) ∧
      (kind ≠ .current → s.ledger.executions.length =
        if (Retained.ordinaryMismatches s.ledger).card ≤ P.tools
        then (Retained.ordinaryMismatches s.ledger).card else 0)

/-- C07: the SAME original I contract may defer physical execution, while
this specified reference executes immediately and uses actual tool 1 (Fin 0).
All costs in the target are true original expected costs. -/
def UniversalFirstCurrentConstruction (P : Star.Parameters) : Prop :=
  ∀ (C : Contract (starInstance P.tools .universalFirst)), C.IsCurrentAllocation →
    ∀ (accounting : NormalAccounting (starInstance P.tools .universalFirst)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
      P.ReferenceLegality .universalFirst .current r none C accounting ∧
      risk (P.input .universalFirst) C .uncapped accounting
        (P.starReferenceRule .universalFirst .current r none (Seed := Unit)) (Measure.dirac ()) ≤ ENNReal.ofReal r ∧
      expectedObservationBill (P.input .universalFirst) C .uncapped accounting
        (P.starReferenceRule .universalFirst .current r none (Seed := Unit)) (Measure.dirac ()) ≤
          ENNReal.ofReal (P.currentObservationEnvelope r) ∧
      P.ImmediateExecution .universalFirst r none C accounting ∧
      P.CurrentToolIdentities .universalFirst r none C accounting ∧
      P.ReferenceAllPathCharges .universalFirst .current r none C accounting

def UniversalFirstEnvelopeAsymptotics (P : Star.Parameters) : Prop :=
  (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → starTargetReal r 1 * min (1 / 4) (r / starTargetReal r 1) ≤ r) ∧
  ∃ bound cutoff : ℝ, 0 ≤ bound ∧ 0 < cutoff ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → r < cutoff →
    |P.currentObservationEnvelope r - P.channel.a * iteratedLog 2 (1 / r)| ≤ bound

/-- C08 includes both ER orders AND the singleton-first I controller,
even when that original I contract demands current physical execution. -/
def CountControllerConstruction (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind),
    (kind = .earlyRetained ∨ (kind = .current ∧ order = .singletonsFirst)) →
    ∀ (C : Contract (starInstance P.tools order)), kind.contracts C →
      ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
        P.ReferenceLegality order kind r none C accounting ∧
        risk (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none (Seed := Unit))
          (Measure.dirac ()) ≤ ENNReal.ofReal r ∧
        expectedObservationBill (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r none (Seed := Unit)) (Measure.dirac ()) ≤
            ENNReal.ofReal (P.countObservationEnvelope P.tools r) ∧
        P.TerminalCriterion order kind r C accounting ∧
        (kind = .earlyRetained → P.RetainedNoEarlyCommitment order kind r none C accounting) ∧
        (kind = .current → P.ImmediateExecution order r none C accounting ∧ P.CurrentToolIdentities order r none C accounting) ∧
        P.ReferenceAllPathCharges order kind r none C accounting

def CountEnvelopeAsymptotics (P : Star.Parameters) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ P.tools → ∃ bound cutoff : ℝ, 0 ≤ bound ∧ 0 < cutoff ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → r < cutoff →
      starTargetReal r k * P.countObservationEnvelope (k - 1) (min (1 / 4) (r / starTargetReal r k)) ≤ bound) ∧
  ∀ k : ℕ, k ≤ P.tools → ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → r < cutoff →
      P.countObservationEnvelope k r ≤ (1 + epsilon) * P.channel.a * iteratedLog (k + 1) (1 / r)

/-- C09: the chronological first bit is tested, in EITHER original order.
The rest are truly blind; terminal repairs occur only with real handles. -/
def LateRetainedConstruction (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (C : Contract (starInstance P.tools order)), C.IsLateRetained →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
      P.ReferenceLegality order .lateRetained r none C accounting ∧
      risk (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none (Seed := Unit))
        (Measure.dirac ()) ≤ ENNReal.ofReal r ∧
      expectedObservationBill (P.input order) C .uncapped accounting
        (P.starReferenceRule order .lateRetained r none (Seed := Unit)) (Measure.dirac ()) ≤
          ENNReal.ofReal (P.channel.a * (Real.log (1 / r) + P.channel.h)) ∧
      (∀ sample n i, i.val ≠ 0 →
        (run (P.input order) C .uncapped accounting (P.starReferenceRule order .lateRetained r none (Seed := Unit))
          sample n).ledger.reviews i = 0) ∧
      P.RetainedNoEarlyCommitment order .lateRetained r none C accounting ∧
      P.TerminalCriterion order .lateRetained r C accounting ∧
      P.ReferenceAllPathCharges order .lateRetained r none C accounting

/-- C10: exact E* and Q*, independent of the certificate from Appendix B or D.
Real delta is not silently identified with a rational runtime parameter. -/
def CommonQuotaArithmetic (P : Star.Parameters) : Prop :=
  (∀ delta : ℝ, 0 < delta → ∃ exponent, IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent) ∧
  (∀ delta : ℚ, 0 < delta →
    IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) (delta : ℝ) (P.commonExponentRat delta)) ∧
  ∀ exponent : ℕ, (2 * (exponent : ℚ) / P.channel.gamma ^ 2) ≤ (P.commonQuota exponent : ℚ)

def CommonTargetFloor (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (delta : ℝ), 0 < delta → delta ≤ 1 / 2 →
      ∀ (limit : Option ℕ) sample n i target,
        let s := run (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind (delta / 2) limit (Seed := Unit)) sample n
        liveStage s i → s.ledger.written i = none →
        P.chosenTargetReal order kind (delta / 2) s.history i = some target →
          delta / 10 ≤ target ∧ target ≤ 1 / 2

section Overflow

variable {Seed : Type u} [MeasurableSpace Seed]

def entryTestEvent (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (stage : (starInstance P.tools order).Stage) (x : Bool)
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) : Set (Seed × (P.input order).World) :=
  {sample | ∃ history target,
    entryHistory (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) stage sample = some history ∧
    (sample.1, history) ∈ B ∧ P.chosenTargetReal order kind r history stage = some target ∧
    (P.input order).truthAt sample.2 stage = x}

def entryOverflowEvent (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ) (quota : ℕ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (stage : (starInstance P.tools order).Stage) (x : Bool)
    (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))) : Set (Seed × (P.input order).World) :=
  {sample | ∃ history target,
    entryHistory (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) stage sample = some history ∧
    (sample.1, history) ∈ B ∧ P.chosenTargetReal order kind r history stage = some target ∧
    (P.input order).truthAt sample.2 stage = x ∧
    (quota : ℕ∞) < realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 stage)}

end Overflow

/-- C11 conditional tail bound, stated on ALL measurable seed/entry-history
events under either truth, rather than only unconditional or successful paths. -/
def ConditionalOverflow (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (delta : ℝ) (exponent : ℕ),
      0 < delta → delta ≤ 1 / 2 → IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent →
      ∀ (Seed : Type u) (m : MeasurableSpace Seed),
        letI : MeasurableSpace Seed := m
        ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
          letI : IsProbabilityMeasure ν := hν
          ∀ (stage : (starInstance P.tools order).Stage) (x : Bool)
            (B : Set (Seed × List (VisibleEvent (starInstance P.tools order)))), MeasurableSet B →
            (P.input order).seededWorldLaw ν
              (P.entryOverflowEvent order kind (delta / 2) (P.commonQuota exponent) C accounting stage x B) ≤
              ENNReal.ofReal (delta / (2 * (P.tools + 1 : ℕ))) *
                (P.input order).seededWorldLaw ν (P.entryTestEvent order kind (delta / 2) C accounting stage x B)

/-- Explicit native-to-local first-exit identity for the fixed ideal script.
This is a target, not an assumed MAP/finite-stopping property of policies. -/
def ReferenceRealFirstExit (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ), 0 < r → r ≤ 1 / 4 →
      ∀ (sample : Unit × (P.input order).World) n i bit,
        let s := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample n
        liveStage s i → s.ledger.written i = none →
        P.starReferenceRule order kind r none () s.history = .write i bit →
          match P.chosenTargetReal order kind r s.history i with
          | none => s.ledger.reviews i = 0 ∧ bit = false
          | some target => realPosteriorStop P.channel.experiment target ((P.input order).reviewAt sample.2 i) =
              ((s.ledger.reviews i).toNat : ℕ∞) ∧
              bit = decide (0 ≤ P.channel.experiment.logOddsScore ((P.input order).reviewAt sample.2 i)
                (s.ledger.reviews i).toNat)

def anyStarOverflow (P : Star.Parameters) (order : Order) (kind : PortKind) (r : ℝ) (quota : ℕ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order)) :
    Set (Unit × (P.input order).World) :=
  ⋃ stage, ⋃ x : Bool, P.entryOverflowEvent order kind r quota C accounting stage x Set.univ

/-- C11's union bound, actual risk coupling and pathwise Q* review bound.
Earlier charges survive the failure path; the inequality is not conditioned
on eventual success. Original H0 is checked separately by qualification. -/
def StarOverflowAssembly (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (delta : ℝ) (exponent : ℕ),
      0 < delta → delta ≤ 1 / 2 → IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent →
      ReviewQuotaCertificate (P.input order) C accounting
        (P.starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)) (Seed := Unit))
        (fun _ => P.commonQuota exponent) ∧
      P.ReferenceAllPathCharges order kind (delta / 2) (some (P.commonQuota exponent)) C accounting ∧
      (P.input order).seededWorldLaw (Measure.dirac ())
        (P.anyStarOverflow order kind (delta / 2) (P.commonQuota exponent) C accounting) ≤ ENNReal.ofReal (delta / 2) ∧
      risk (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)) (Seed := Unit)) (Measure.dirac ()) ≤
          risk (P.input order) C .uncapped accounting
            (P.starReferenceRule order kind (delta / 2) none (Seed := Unit)) (Measure.dirac ()) +
              (P.input order).seededWorldLaw (Measure.dirac ())
                (P.anyStarOverflow order kind (delta / 2) (P.commonQuota exponent) C accounting)

/-- Actual same-tape states coincide through the overflow prefix. The
bounded run then abandons and retains the complete already-paid ledger. -/
def SameTapeStarTruncation (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (r : ℝ) (quota : ℕ), 0 < r → r ≤ 1 / 4 →
      ∀ sample : Unit × (P.input order).World,
        let ideal := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample
        let bounded := run (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) sample
        ((∀ n, bounded n = ideal n) ∨ ∃ cut,
          (∀ n, n ≤ cut → bounded n = ideal n) ∧ (ideal cut).halted = false ∧
          bounded (cut + 1) = stopState (ideal cut) true ∧
          ∀ n, bounded (cut + 1 + n) = stopState (ideal cut) true) ∧
        runActualBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r (some quota)) sample ≤
          runActualBill (P.input order) C .uncapped accounting (P.starReferenceRule order kind r none) sample

def RationalStarImplementation (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (r : ℚ), 0 < r → r ≤ 1 / 4 →
    ∀ limit history, P.starRationalRule order kind r limit () history =
      P.starReferenceRule order kind (r : ℝ) limit () history

/-- Native policy existence, legality, exact original-risk guarantee and
cost domination are CONCLUSIONS under the original Q/H/actual H0 certificate. -/
def NativeStarImplementation (P : Star.Parameters) : Prop :=
  ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
    ∀ (accounting : NormalAccounting (starInstance P.tools order)) (delta : ℝ) (exponent : ℕ),
      0 < delta → delta ≤ 1 / 2 → P.OriginalStarQualification order kind delta exponent C accounting →
        ∃ policy : Policy (P.input order) C .native accounting Unit,
          policy.rule = P.starReferenceRule order kind (delta / 2) (some (P.commonQuota exponent)) ∧
          risk (P.input order) C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
          expectedBill (P.input order) C .native accounting policy.rule (Measure.dirac ()) ≤
            expectedBill (P.input order) C .uncapped accounting
              (P.starReferenceRule order kind (delta / 2) none (Seed := Unit)) (Measure.dirac ())

/-- C12, fixed P FIRST, then one cutoff uniform in both orders, all three
contracts, their ORIGINAL caps and qualified accounting. The value remains
Native.value over ALL randomized policies, not these reference rules. -/
def ThreePrices (P : Star.Parameters) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ delta : ℝ, 0 < delta → delta < cutoff → delta ≤ 1 / 2 →
      ∀ (order : Order) (kind : PortKind), 0 < P.leadingScale order kind delta ∧
        ∀ (C : Contract (starInstance P.tools order)), kind.contracts C →
          ∀ (accounting : NormalAccounting (starInstance P.tools order)) (exponent : ℕ),
            P.OriginalStarQualification order kind delta exponent C accounting →
              ENNReal.ofReal ((1 - epsilon) * P.leadingScale order kind delta) ≤
                P.value order C .native accounting (ENNReal.ofReal delta) ∧
              P.value order C .native accounting (ENNReal.ofReal delta) ≤
                ENNReal.ofReal ((1 + epsilon) * P.leadingScale order kind delta)

/-- The lower comparison is cap independent and never assumes the selected
controller's H0 certificate. No finite-cost/ET, MAP or feasibility condition
is inserted into the native value comparator. -/
def ThreePricesLower (P : Star.Parameters) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ delta : ℝ, 0 < delta → delta < cutoff →
      ∀ (order : Order) (kind : PortKind) (C : Contract (starInstance P.tools order)), kind.contracts C →
        ∀ accounting, ENNReal.ofReal ((1 - epsilon) * P.leadingScale order kind delta) ≤
          P.value order C .native accounting (ENNReal.ofReal delta)

def C07Claims (P : Star.Parameters) : Prop :=
  P.UniversalFirstCurrentConstruction ∧ P.UniversalFirstEnvelopeAsymptotics

def C08Claims (P : Star.Parameters) : Prop := P.CountControllerConstruction ∧ P.CountEnvelopeAsymptotics

def C09Claims (P : Star.Parameters) : Prop := P.LateRetainedConstruction

def C10Claims (P : Star.Parameters) : Prop := P.CommonQuotaArithmetic ∧ P.CommonTargetFloor

def C11Claims (P : Star.Parameters) : Prop :=
  P.ConditionalOverflow.{u} ∧ P.StarOverflowAssembly ∧ P.SameTapeStarTruncation ∧
    P.RationalStarImplementation ∧ P.NativeStarImplementation

def C12Claims (P : Star.Parameters) : Prop := P.ThreePrices ∧ P.ThreePricesLower

def ExplicitStarClaims (P : Star.Parameters) : Prop :=
  P.ReferenceRealFirstExit ∧ P.C07Claims ∧ P.C08Claims ∧ P.C09Claims ∧ P.C10Claims ∧ P.C11Claims.{u} ∧ P.C12Claims

end Parameters
end PaperProofs.Star
