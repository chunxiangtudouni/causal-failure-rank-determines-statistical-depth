module

public import PaperProofs.Paid.MultiplierSearch
public import PaperProofs.Common.NormalCharges

/-! Fixed calibrated backend of frozen paid-proofs.tex:563--612.
The rational walk table, coins, stopped local tests and visible-history
compiler are actual independent data. Performance, exact calibration,
guard nonbinding and original-cap feasibility remain separate Prop targets.
The original multiplier table and initial whole-policy selector are retained.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.Parameters

open Common Common.Native Statistics

abbrev WalkCell (level : ℕ) := Fin (2 * level + 1)

def walkMove (level : ℕ) (state : WalkCell level) (letter : Fin 2) : WalkCell level :=
  if hboundary : state.val = 0 ∨ state.val = 2 * level then state else
  if letter.val = 1 then ⟨state.val + 1, by omega⟩ else ⟨state.val - 1, by omega⟩

/-- One actual finite-array birth-death update, with two outgoing letters
per cell. Absorbed boundary mass stays at that boundary. -/
def walkUpdate (P : PaperProofs.Paid.Parameters) (level : ℕ) (truth : Bool) (previous : Array ℚ) : Array ℚ :=
  (List.finRange (2 * level + 1)).foldl (fun next state =>
    (List.finRange 2).foldl (fun next letter =>
      let target := walkMove level state letter
      next.setIfInBounds target.val
        (next.getD target.val 0 + previous.getD state.val 0 * P.experiment.channel truth letter)) next)
    (Array.replicate (2 * level + 1) 0)

/-- The finite absorbing random-walk table stores its preceding row once.
It never consults the actual test error or a performance oracle. -/
def walkRow (P : PaperProofs.Paid.Parameters) (level : ℕ) (truth : Bool) : ℕ → Array ℚ
  | 0 => Array.ofFn (fun state : WalkCell level => if state.val = level then 1 else 0)
  | steps + 1 => P.walkUpdate level truth (P.walkRow level truth steps)

def walkDistribution (P : PaperProofs.Paid.Parameters) (level : ℕ) (truth : Bool) (steps : ℕ)
    (state : WalkCell level) : ℚ := (P.walkRow level truth steps).getD state.val 0

/-- MAP loss at Q after absorption, with an independent fair tie. -/
def cappedError (P : PaperProofs.Paid.Parameters) (m : ℕ) : ℚ :=
  ∑ state : WalkCell (m + 1), P.walkDistribution (m + 1) true P.certificate.Q state *
    if state.val < m + 1 then 1 else if state.val = m + 1 then 1 / 2 else 0

def calibrationWeight (P : PaperProofs.Paid.Parameters) (m : ℕ) : ℚ :=
  (1 / 2 - P.binarySymmetric.endpointError m) / (1 / 2 - P.cappedError m)

/-- Totalization on unverified/malformed indices only. D24's valid-index
target proves that the original rational omega itself lies in [0,1]. -/
def clippedCalibrationWeight (P : PaperProofs.Paid.Parameters) (m : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (P.calibrationWeight m : ℝ)), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

noncomputable def cappedStop (P : PaperProofs.Paid.Parameters) (m : ℕ) (tape : P.binarySymmetric.experiment.Tape) : ℕ∞ :=
  min (P.binarySymmetric.experiment.posteriorThresholdStop (P.binarySymmetric.endpointError (m + 1)) tape)
    (P.certificate.Q : ℕ∞)

noncomputable def cappedDecision (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (tie : Bool) (tape : P.binarySymmetric.experiment.Tape) : Bool :=
  let score := P.binarySymmetric.experiment.logOddsScore tape (P.cappedStop m tape).toNat
  if score = 0 then tie else decide (0 ≤ score)

theorem cappedStop_le (P : PaperProofs.Paid.Parameters) (m : ℕ) (tape : P.binarySymmetric.experiment.Tape) :
    P.cappedStop m tape ≤ P.certificate.Q := min_le_right _ _

theorem cappedStop_ne_top (P : PaperProofs.Paid.Parameters) (m : ℕ) (tape : P.binarySymmetric.experiment.Tape) :
    P.cappedStop m tape ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) (P.cappedStop_le m tape)

theorem measurable_cappedStop (P : PaperProofs.Paid.Parameters) (m : ℕ) : Measurable (P.cappedStop m) := by
  have ht : Measurable (fun tape : P.binarySymmetric.experiment.Tape =>
      P.binarySymmetric.experiment.posteriorThresholdStop (P.binarySymmetric.endpointError (m + 1)) tape) :=
    P.binarySymmetric.experiment.measurable_posteriorThresholdStop (P.binarySymmetric.endpointError (m + 1))
  unfold cappedStop
  exact (measurable_of_countable (fun time : ℕ∞ => min time (P.certificate.Q : ℕ∞))).comp ht

/-- A real causal bounded test; exact error and mean-cost claims are not fields. -/
noncomputable def cappedTest (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.binarySymmetric.experiment.AdmissibleRule Bool where
  rule := {
    stop := fun _ tape => P.cappedStop m tape
    decision := P.cappedDecision m
    stopping := by
      intro seed tape tape' n hp
      simp only [cappedStop, min_le_iff]
      rw [P.binarySymmetric.experiment.posteriorThresholdStop_stopping (P.binarySymmetric.endpointError (m + 1))
        () tape tape' n hp]
    stoppedDecision := by
      intro seed tape tape' n hs hs' hp
      simp only [cappedDecision, hs, hs', ENat.toNat_natCast]
      rw [P.binarySymmetric.experiment.logOddsScore_eq_of_prefix tape tape' n hp] }
  measurable_stop := (P.measurable_cappedStop m).comp measurable_snd
  measurable_decision := by
    have hn : Measurable (fun sample : Bool × P.binarySymmetric.experiment.Tape => (P.cappedStop m sample.2).toNat) :=
      (measurable_of_countable ENat.toNat).comp
        ((P.measurable_cappedStop m).comp measurable_snd)
    have hjoint : Measurable (fun pair : P.binarySymmetric.experiment.Tape × ℕ =>
        P.binarySymmetric.experiment.logOddsScore pair.1 pair.2) :=
      measurable_from_prod_countable_left (fun n => P.binarySymmetric.experiment.measurable_logOddsScore n)
    have hscore := hjoint.comp (measurable_snd.prodMk hn)
    have hsign : Measurable (fun sample : Bool × P.binarySymmetric.experiment.Tape =>
        decide (0 ≤ P.binarySymmetric.experiment.logOddsScore sample.2 (P.cappedStop m sample.2).toNat)) := by
      apply measurable_to_bool
      simpa only [Function.comp_def, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
        measurableSet_le measurable_const hscore
    exact Measurable.ite (measurableSet_eq_fun hscore measurable_const) measurable_fst hsign

/-- The first independent coin chooses capped versus blind; the second
is the fair guess and the fair terminal tie, used on mutually exclusive branches. -/
noncomputable def calibratedTest (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.binarySymmetric.experiment.AdmissibleRule (Bool × Bool) :=
  (fun lower upper : P.binarySymmetric.experiment.AdmissibleRule Bool => ({
    rule := {
      stop := fun seed tape => if seed.1 then lower.rule.stop seed.2 tape else upper.rule.stop seed.2 tape
      decision := fun seed tape => if seed.1 then lower.rule.decision seed.2 tape else upper.rule.decision seed.2 tape
      stopping := by
        intro seed tape tape' n hp
        cases hb : seed.1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte]
        · exact upper.rule.stopping seed.2 tape tape' n hp
        · exact lower.rule.stopping seed.2 tape tape' n hp
      stoppedDecision := by
        intro seed tape tape' n hs hs' hp
        cases hb : seed.1 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs hs' ⊢
        · exact upper.rule.stoppedDecision seed.2 tape tape' n hs hs' hp
        · exact lower.rule.stoppedDecision seed.2 tape tape' n hs hs' hp }
    measurable_stop := by
      have hp : Measurable (fun sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape => (sample.1.2, sample.2)) :=
        measurable_fst.snd.prodMk measurable_snd
      exact Measurable.ite (measurable_fst.fst (measurableSet_singleton true))
        (lower.measurable_stop.comp hp) (upper.measurable_stop.comp hp)
    measurable_decision := by
      have hp : Measurable (fun sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape => (sample.1.2, sample.2)) :=
        measurable_fst.snd.prodMk measurable_snd
      exact Measurable.ite (measurable_fst.fst (measurableSet_singleton true))
        (lower.measurable_decision.comp hp) (upper.measurable_decision.comp hp)
    } : P.binarySymmetric.experiment.AdmissibleRule (Bool × Bool)))
    (if m = 0 then P.binarySymmetric.fairGuessTest else P.cappedTest m) P.binarySymmetric.fairGuessTest

noncomputable def calibrationSeedLaw (P : PaperProofs.Paid.Parameters) (m : ℕ) : Measure (Bool × Bool) :=
  (BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight m)).prod BinarySymmetric.Parameters.fairGuessLaw

instance calibrationSeedLaw_probability (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    IsProbabilityMeasure (P.calibrationSeedLaw m) := by
  unfold calibrationSeedLaw
  infer_instance

/-- D23: the actual cap at level m+1, original tail chain, and strict room
for calibration. No Hoeffding or error bound is an input field. -/
def BoundedEndpointClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ P.certificate.M →
    (∀ x : Bool,
      P.binarySymmetric.experiment.conditionalLaw BinarySymmetric.Parameters.fairGuessLaw x
        {sample | (P.binarySymmetric.symmetricHittingTest (m + 1)).rule.stop () sample.2 > P.certificate.Q} ≤
          ENNReal.ofReal (Real.exp (-(P.certificate.gamma : ℝ)^2 * P.certificate.Q / 2))) ∧
    Real.exp (-(P.certificate.gamma : ℝ)^2 * P.certificate.Q / 2) ≤ Real.exp (-(P.certificate.E : ℝ)) ∧
    Real.exp (-(P.certificate.E : ℝ)) ≤ (1 / 2 : ℝ) ^ P.certificate.E ∧
    (1 / 2 : ℚ) ^ P.certificate.E ≤ P.certificate.gamma * P.certificate.epsilon ∧
    (∀ x : Bool, P.binarySymmetric.experiment.conditionalError BinarySymmetric.Parameters.fairGuessLaw (P.cappedTest m) x =
      ENNReal.ofReal (P.cappedError m : ℝ)) ∧
    0 ≤ P.cappedError m ∧
    P.binarySymmetric.endpointError (m + 1) ≤ (1 - 2 * P.certificate.gamma) * P.binarySymmetric.endpointError m ∧
    P.cappedError m ≤ P.binarySymmetric.endpointError (m + 1) + P.certificate.gamma * P.certificate.epsilon ∧
    P.binarySymmetric.endpointError (m + 1) + P.certificate.gamma * P.certificate.epsilon ≤
      P.binarySymmetric.endpointError m - P.certificate.gamma * P.certificate.epsilon ∧
    P.cappedError m < P.binarySymmetric.endpointError m

/-- D24: q_m is the independent finite rational DP, and both actual
truth-conditional errors (not just the Bayes average) are p_m. -/
def ExactCalibrationClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  (∀ x : Bool, P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw 0) (P.calibratedTest 0) x =
    ENNReal.ofReal (P.binarySymmetric.endpointError 0 : ℝ)) ∧
  (∀ sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape, (P.calibratedTest 0).rule.stop sample.1 sample.2 = 0) ∧
  (∀ x : Bool, P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw 0) (P.calibratedTest 0) x = 0) ∧
  ∀ m : ℕ, 1 ≤ m → m ≤ P.certificate.M →
    0 ≤ P.calibrationWeight m ∧ P.calibrationWeight m ≤ 1 ∧
    (P.clippedCalibrationWeight m).val = (P.calibrationWeight m : ℝ) ∧
    (∀ x : Bool, P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw m) (P.calibratedTest m) x =
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ)) ∧
    (∀ sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape,
      (P.calibratedTest m).rule.stop sample.1 sample.2 ≤ P.certificate.Q) ∧
    (∀ x : Bool, P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw m) (P.calibratedTest m) x ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge (m + 1) : ℝ)) ∧
    P.binarySymmetric.endpointCharge (m + 1) ≤ 4 * P.binarySymmetric.endpointCharge m

abbrev CalibrationMarks (P : PaperProofs.Paid.Parameters) :=
  P.sharedInstance.Stage → Fin (P.certificate.M + 1) → Bool

abbrev CalibratedMenuSeed (P : PaperProofs.Paid.Parameters) :=
  MenuSeed P.certificate.stages P.tools × P.CalibrationMarks

abbrev CalibratedSearchSeed (P : PaperProofs.Paid.Parameters) := Bool × P.CalibratedMenuSeed

/-- Independent marks for every potential stage/level pair. Only the one
stored entry selected at that stage is read. The separate fair stage bit
is used for blind guesses and terminal ties. These are private seeds, not
native actions or observations of any hidden truth. -/
noncomputable def calibrationMarksLaw (P : PaperProofs.Paid.Parameters) : Measure P.CalibrationMarks :=
  Measure.pi fun _stage => Measure.pi fun level : Fin (P.certificate.M + 1) =>
    BinarySymmetric.Parameters.rocCoinLaw (P.clippedCalibrationWeight level.val)

noncomputable def calibratedMenuSeedLaw (P : PaperProofs.Paid.Parameters) : Measure P.CalibratedMenuSeed :=
  (menuSeedLaw P.certificate.stages P.tools).prod P.calibrationMarksLaw

instance calibrationMarksLaw_probability (P : PaperProofs.Paid.Parameters) : IsProbabilityMeasure P.calibrationMarksLaw := by
  unfold calibrationMarksLaw
  infer_instance

instance calibratedMenuSeedLaw_probability (P : PaperProofs.Paid.Parameters) : IsProbabilityMeasure P.calibratedMenuSeedLaw := by
  unfold calibratedMenuSeedLaw
  infer_instance

/-- The actual selected stage/level mark and its independent fair bit
have exactly the local calibration seed law. The statement is about the
fixed product seed, not a conditional-risk assertion or a seed oracle. -/
def CalibrationMarksClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (stage : P.sharedInstance.Stage) (level : Fin (P.certificate.M + 1)),
    P.calibratedMenuSeedLaw.map (fun seed => (seed.2 stage level, seed.1 stage)) = P.calibrationSeedLaw level.val

def cappedTestingAction (P : PaperProofs.Paid.Parameters) (m : ℕ) (tie : Bool)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) : Action P.sharedInstance :=
  let observations := historyObservations history stage
  if observations.all (fun symbol => symbol < 2) then
    let score := menuWordScore observations
    if m + 1 ≤ score.natAbs ∨ P.certificate.Q ≤ observations.length then
      .write stage (if score = 0 then tie else decide (0 ≤ score))
    else .review stage
  else .abandon

def calibratedTestingAction (P : PaperProofs.Paid.Parameters) (level : ℕ) (seed : P.CalibratedMenuSeed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) : Action P.sharedInstance :=
  if level = 0 then .write stage (seed.1 stage) else
  if hlevel : level ≤ P.certificate.M then
    if seed.2 stage ⟨level, by omega⟩ then P.cappedTestingAction level (seed.1 stage) history stage
    else .write stage (seed.1 stage)
  else .abandon

@[simp] theorem calibratedTestingAction_zero (P : PaperProofs.Paid.Parameters) (seed : P.CalibratedMenuSeed)
    (history : List (VisibleEvent P.sharedInstance)) (stage : P.sharedInstance.Stage) :
    P.calibratedTestingAction 0 seed history stage = .write stage (seed.1 stage) := by
  simp only [calibratedTestingAction, ↓reduceIte]

/-- Same stored endpoint action and actual repair choice as the old menu.
Only its local review/write implementation is replaced. No risk, mean
cost, search convergence, or cap certificate is consulted by this script. -/
def calibratedMenuCandidate (P : PaperProofs.Paid.Parameters) (table : MenuTable)
    (seed : P.CalibratedMenuSeed) (history : List (VisibleEvent P.sharedInstance)) : Action P.sharedInstance :=
  if historyHalted history then .stop else
  if hstage : historyCursor history < P.certificate.stages then
    let stage : P.sharedInstance.Stage := ⟨historyCursor history, by simpa [sharedInstance] using hstage⟩
    let entry := menuEntryAt table (P.certificate.stages - stage.val)
      (P.menuEntryTools P.certificate.stages P.tools history stage)
    match historyWrite history stage with
    | none => match entry.action with
      | .finish | .abandon => .abandon
      | .test level _ => P.calibratedTestingAction level seed history stage
    | some (bit, serial) => match historyReport history stage with
      | none => .abandon
      | some (truth, reportedSerial) =>
          if serial != reportedSerial then .abandon else
          if bit == truth then .advance stage else
          match entry.action with
          | .test _ .repair => P.menuRepairAction P.certificate.stages P.tools history stage
          | _ => .abandon
  else if historyCursor history = P.certificate.stages then .stop else .abandon

def calibratedStateCandidate (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    PolicyRule P.sharedInstance P.CalibratedSearchSeed :=
  fun seed history => match state with
  | .exact solution => P.calibratedMenuCandidate solution.table seed.2 history
  | .bracket lower upper =>
      P.calibratedMenuCandidate (if seed.1 then lower.table else upper.table) seed.2 history

def calibratedStateRule (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    PolicyRule P.sharedInstance P.CalibratedSearchSeed := searchGuardRule (P.calibratedStateCandidate state)

noncomputable def calibratedStateSeedLaw (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    Measure P.CalibratedSearchSeed :=
  (BinarySymmetric.Parameters.rocCoinLaw (P.stateWeight state)).prod P.calibratedMenuSeedLaw

instance calibratedStateSeedLaw_probability (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    IsProbabilityMeasure (P.calibratedStateSeedLaw state) := by
  unfold calibratedStateSeedLaw
  infer_instance

def calibratedStatePolicy (P : PaperProofs.Paid.Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting P.CalibratedSearchSeed where
  rule := P.calibratedStateRule state
  measurable_rule := measurable_of_countable _
  legal := searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting (P.calibratedStateCandidate state)

/-- Same offline multiplier-search output and original zero-charge branch.
The original endpoint tables are never recalculated from test durations. -/
def calibratedAlgorithmCandidate (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    PolicyRule P.sharedInstance P.CalibratedSearchSeed :=
  if P.zeroChargeRisk fee ≤ P.certificate.risk then
    fun seed history => P.zeroChargeCandidateRule fee seed.2.1 history
  else P.calibratedStateCandidate (P.idealSearchState fee)

def calibratedAlgorithmRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    PolicyRule P.sharedInstance P.CalibratedSearchSeed := searchGuardRule (P.calibratedAlgorithmCandidate fee)

noncomputable def calibratedAlgorithmSeedLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Measure P.CalibratedSearchSeed :=
  if P.zeroChargeRisk fee ≤ P.certificate.risk then (Measure.dirac false).prod P.calibratedMenuSeedLaw
  else P.calibratedStateSeedLaw (P.idealSearchState fee)

instance calibratedAlgorithmSeedLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    IsProbabilityMeasure (P.calibratedAlgorithmSeedLaw fee) := by
  unfold calibratedAlgorithmSeedLaw
  split_ifs <;> infer_instance

def calibratedAlgorithmPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting P.CalibratedSearchSeed where
  rule := P.calibratedAlgorithmRule fee
  measurable_rule := measurable_of_countable _
  legal := searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting (P.calibratedAlgorithmCandidate fee)

/-- Genuine H0 test for THIS fixed backend, on the same original C and
accounting. It contains no risk/cost/ET/optimality or target conclusion. -/
def CalibratedOriginalQualification (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) : Prop :=
  P.NativeCapQualification C ∧ NormalCallCertificate (P.input fee hfee) C.val .uncapped accounting
    (P.calibratedAlgorithmPolicy fee hfee C accounting) C.val.normalCallBound

/-- Actual eventually written correct/wrong flags, actual physical
stage-tool execution choices, and ultimate failure. Clocks and excess
observations are deliberately absent, as in the source's stored policy.
Unvisited stages have neither write flag; no future guesses are inserted. -/
abbrev ExecutionSignature (P : PaperProofs.Paid.Parameters) :=
  (P.sharedInstance.Stage → Bool) × (P.sharedInstance.Stage → Bool) ×
    (P.sharedInstance.Stage → P.sharedInstance.Tool → Bool) × Bool

section Outcome

variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def eventualFlag (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (predicate : State P.sharedInstance → Prop)
    (sample : Seed × (P.input fee hfee).World) : Bool := by
  classical
  exact decide (∃ n, predicate (run (P.input fee hfee) C.val mode accounting rule sample n))

theorem measurable_eventualFlag (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (predicate : State P.sharedInstance → Prop) :
    Measurable (P.eventualFlag fee hfee C mode accounting rule predicate) := by
  classical
  apply measurable_to_bool
  have hmeas : MeasurableSet {sample : Seed × (P.input fee hfee).World |
      ∃ n, predicate (run (P.input fee hfee) C.val mode accounting rule sample n)} := by
    have heq : {sample : Seed × (P.input fee hfee).World |
        ∃ n, predicate (run (P.input fee hfee) C.val mode accounting rule sample n)} =
        ⋃ n : ℕ, {sample | predicate (run (P.input fee hfee) C.val mode accounting rule sample n)} := by
      ext sample
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [heq]
    exact MeasurableSet.iUnion fun n => (measurable_run (P.input fee hfee) C.val mode accounting rule hm n)
      (MeasurableSpace.measurableSet_top (s := {state | predicate state}))
  simpa only [eventualFlag, Function.comp_def, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using hmeas

noncomputable def executionSignature (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) : P.ExecutionSignature := by
  classical
  exact (fun i => P.eventualFlag fee hfee C mode accounting rule (fun state => state.ledger.written i = some (state.ledger.truth i)) sample,
    fun i => P.eventualFlag fee hfee C mode accounting rule (fun state => state.ledger.written i = some (!state.ledger.truth i)) sample,
    (fun i tool => P.eventualFlag fee hfee C mode accounting rule (fun state =>
      ∃ e ∈ state.ledger.executions, e.handle.stage = i ∧ e.tool = tool) sample),
    decide (¬ runSuccess (P.input fee hfee) C.val mode accounting rule sample))

theorem measurable_executionSignature (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    Measurable (P.executionSignature fee hfee C mode accounting rule) := by
  classical
  have hfailure : Measurable (fun sample : Seed × (P.input fee hfee).World =>
      decide (¬ runSuccess (P.input fee hfee) C.val mode accounting rule sample)) := by
    apply measurable_to_bool
    simpa only [Function.comp_def, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Set.compl_ofPred] using
      (measurableSet_runSuccess (P.input fee hfee) C.val mode accounting rule hm).compl
  exact (measurable_pi_iff.mpr (fun _ => P.measurable_eventualFlag fee hfee C mode accounting rule hm _)).prodMk
    ((measurable_pi_iff.mpr (fun _ => P.measurable_eventualFlag fee hfee C mode accounting rule hm _)).prodMk
      ((measurable_pi_iff.mpr (fun _ => measurable_pi_iff.mpr (fun _ =>
        P.measurable_eventualFlag fee hfee C mode accounting rule hm _))).prodMk hfailure))

noncomputable def executionSignatureLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) : Measure P.ExecutionSignature :=
  ((P.input fee hfee).seededWorldLaw ν).map (P.executionSignature fee hfee C mode accounting rule)

noncomputable def runActualCorrectionBill (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hfee).World) : ℝ≥0∞ :=
  ⨆ n, (run (P.input fee hfee) C.val mode accounting rule sample n).ledger.correctionBill (P.input fee hfee).fees

theorem measurable_runActualCorrectionBill (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) :
    Measurable (P.runActualCorrectionBill fee hfee C mode accounting rule) := by
  apply Measurable.iSup
  intro n
  exact (measurable_of_countable (fun state : State P.sharedInstance =>
    state.ledger.correctionBill (P.input fee hfee).fees)).comp
      (measurable_run (P.input fee hfee) C.val mode accounting rule hm n)

/-- Full distribution of ACTUAL paid corrections on every path, including
those paid before eventual failure, abandonment, or nonreturn. -/
noncomputable def actualCorrectionBillLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) : Measure ℝ≥0∞ :=
  ((P.input fee hfee).seededWorldLaw ν).map (P.runActualCorrectionBill fee hfee C mode accounting rule)

noncomputable def expectedActualCorrectionBill (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (ν : Measure Seed) : ℝ≥0∞ :=
  ∫⁻ sample, P.runActualCorrectionBill fee hfee C mode accounting rule sample ∂(P.input fee hfee).seededWorldLaw ν

end Outcome

def recordedStateCost (P : PaperProofs.Paid.Parameters) (fee : ℚ) : MultiplierState → ℚ
  | .exact solution => P.solveCost fee solution
  | .bracket lower upper => P.mixtureCost fee lower upper

/-- D25 is about this actual generated state and its fixed calibrated
runtime. The equality is of the complete discrete outcome law; actual
correction fees paid before failure are also asserted equal separately.
No endpoint-optimality or calibration performance is a premise. -/
def CalibratedImplementationClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ),
    let state := P.multiplierSearch fee steps
    P.executionSignatureLaw fee hfee C .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
      P.executionSignatureLaw fee hfee C .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    risk (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
      risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    P.actualCorrectionBillLaw fee hfee C .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
      P.actualCorrectionBillLaw fee hfee C .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    P.expectedActualCorrectionBill fee hfee C .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) =
      P.expectedActualCorrectionBill fee hfee C .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) ≤
      4 * expectedObservationBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) ≤
      4 * expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting (P.calibratedStateRule state) (P.calibratedStateSeedLaw state) ≤
      4 * ENNReal.ofReal (P.recordedStateCost fee state : ℝ)

/-- D26's resources belong to one chosen whole-policy branch, rather
than adding the resources of both branches of its initial selector. H0
is the genuine fixed-script assumption above; all other bounds are targets. -/
def CalibratedNativeEightClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance),
    (∀ (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (n : ℕ),
      (∀ i, (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n).ledger.reviews i ≤
        (P.certificate.Q : ℕ∞)) ∧
      (∑ i, (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n).ledger.reviews i) ≤
        (P.certificate.stages * P.certificate.Q : ℕ) ∧
      (run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n).ledger.executions.length ≤ P.tools) ∧
    (P.CalibratedOriginalQualification fee hfee C accounting →
      ∃ policy : Policy (P.input fee hfee) C.val .native accounting P.CalibratedSearchSeed,
        policy.rule = P.calibratedAlgorithmRule fee ∧
        (∀ sample n, run (P.input fee hfee) C.val .native accounting policy.rule sample n =
          run (P.input fee hfee) C.val .uncapped accounting (P.calibratedAlgorithmRule fee) sample n) ∧
        risk (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤ P.targetRisk ∧
        P.uncappedValue C accounting fee hfee ≤ P.nativeValue C accounting fee hfee ∧
        P.nativeValue C accounting fee hfee ≤
          expectedBill (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ∧
        expectedBill (P.input fee hfee) C.val .native accounting policy.rule (P.calibratedAlgorithmSeedLaw fee) ≤
          8 * P.uncappedValue C accounting fee hfee)

def CalibratedBackendClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.BoundedEndpointClaims ∧ P.ExactCalibrationClaims ∧ P.CalibrationMarksClaims ∧
    P.CalibratedImplementationClaims ∧ P.CalibratedNativeEightClaims

end PaperProofs.Paid.Parameters
