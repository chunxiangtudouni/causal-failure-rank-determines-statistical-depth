module

public import PaperProofs.Paid.MenuCompiler
public import PaperProofs.Statistics.ControllerThresholds
public import Mathlib.Data.Nat.Choose.Basic

/-!
The actual rational multiplier search and initial whole-policy mixture from
paid-proofs.tex:486--561. Every solve calls the already independent finite
menu compiler. Stored records are executable data, not assumed optimality
certificates. D19--D22 below are explicit pending propositions.

This is the IDEAL unbounded-endpoint algorithm. Its endpoint tests have not
been replaced by D23--D25's calibrated bounded backend; no Q/H0 certificate
or native upper guarantee is inferred for this endpoint search.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid

open Common Common.Native

universe u

/-- No optimality or risk assertion is a field of a solve. -/
structure MultiplierSolve where
  multiplier : ℚ
  table : MenuTable
  deriving DecidableEq, Repr

inductive MultiplierState where
  | bracket (lower upper : MultiplierSolve)
  | exact (solution : MultiplierSolve)
  deriving DecidableEq, Repr

/-- A visible permission guard, without a statistical or resource oracle. -/
def searchGuardRule {I : Instance} {Seed : Type*} (candidate : PolicyRule I Seed) : PolicyRule I Seed :=
  fun seed history =>
    let action := candidate seed history
    if historyAllowsAction history action then action else .abandon

theorem searchGuardRule_uncapped_legal {I : Instance} {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (candidate : PolicyRule I Seed) :
    LegalRule input C .uncapped accounting (searchGuardRule candidate) := by
  intro seed truth tapes n state hp hactive
  let action := candidate seed state.history
  by_cases allowed : historyAllowsAction state.history action
  · obtain ⟨next, step⟩ := historyAllowsAction_sound input C hearly accounting
      (searchGuardRule candidate) seed truth tapes hp hactive action allowed
    exact ⟨next, by simpa only [searchGuardRule, action, ite_eq_left allowed] using step⟩
  · exact ⟨stopState state true, by
      simpa only [searchGuardRule, action, ite_eq_right allowed] using
        (Step.abandon (input := input) (C := C) (mode := ResourceMode.uncapped)
          (accounting := accounting) (tapes := tapes) state hactive)⟩

theorem searchRun_seed_rule_eq {I : Instance} {Seed Seed' : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Seed'] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (rule' : PolicyRule I Seed')
    (seed : Seed) (seed' : Seed') (h : ∀ history, rule seed history = rule' seed' history)
    (world : input.World) (n : ℕ) :
    run input C mode accounting rule (seed, world) n = run input C mode accounting rule' (seed', world) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, ih, h]

theorem searchBill_seed_rule_eq {I : Instance} {Seed Seed' : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Seed'] (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (rule' : PolicyRule I Seed')
    (seed : Seed) (seed' : Seed') (h : ∀ history, rule seed history = rule' seed' history)
    (world : input.World) :
    runActualBill input C mode accounting rule (seed, world) = runActualBill input C mode accounting rule' (seed', world) := by
  unfold runActualBill
  apply iSup_congr
  intro n
  rw [searchRun_seed_rule_eq input C mode accounting rule rule' seed seed' h world n]

namespace Parameters

abbrev SearchSeed (P : PaperProofs.Paid.Parameters) := Bool × MenuSeed P.certificate.stages P.tools

def solveMultiplier (P : PaperProofs.Paid.Parameters) (fee multiplier : ℚ) : MultiplierSolve :=
  ⟨multiplier, P.solveMenuTable fee multiplier P.tools P.certificate.stages⟩

def solveRecord (P : PaperProofs.Paid.Parameters) (solution : MultiplierSolve) : MenuEntry :=
  menuEntryAt solution.table P.certificate.stages P.tools

def solveRisk (P : PaperProofs.Paid.Parameters) (solution : MultiplierSolve) : ℚ :=
  (P.solveRecord solution).failure

/-- Actual observation cost plus f times the actual-execution mean. -/
def solveCost (P : PaperProofs.Paid.Parameters) (fee : ℚ) (solution : MultiplierSolve) : ℚ :=
  (P.solveRecord solution).observation + fee * (P.solveRecord solution).repairs

def solveRule (P : PaperProofs.Paid.Parameters) (solution : MultiplierSolve) :
    PolicyRule P.sharedInstance (MenuSeed P.certificate.stages P.tools) :=
  P.compiledMenuRule P.certificate.stages P.tools solution.table

@[simp] theorem solveMultiplier_rule (P : PaperProofs.Paid.Parameters) (fee multiplier : ℚ) :
    P.solveRule (P.solveMultiplier fee multiplier) = P.paidEndpointRule fee multiplier := rfl

def initialMultiplierState (P : PaperProofs.Paid.Parameters) (fee : ℚ) : MultiplierState :=
  .bracket (P.solveMultiplier fee 0) (P.solveMultiplier fee P.Lambda)

def mixtureWeight (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve) : ℚ :=
  (P.certificate.risk - P.solveRisk upper) / (P.solveRisk lower - P.solveRisk upper)

def mixtureCost (P : PaperProofs.Paid.Parameters) (fee : ℚ) (lower upper : MultiplierSolve) : ℚ :=
  let weight := P.mixtureWeight lower upper
  weight * P.solveCost fee lower + (1 - weight) * P.solveCost fee upper

/-- A rational version of F(lambda_U)-lambda_U delta. Its equality to the
independent full-policy F is a TARGET, never the definition of F. -/
def mixtureLower (P : PaperProofs.Paid.Parameters) (fee : ℚ) (upper : MultiplierSolve) : ℚ :=
  (P.solveRecord upper).objective fee upper.multiplier - upper.multiplier * P.certificate.risk

/-- Only a total completion on malformed brackets. The actual reachable
bracket theorem below asserts that this clipping leaves w unchanged. -/
def clippedMixtureWeight (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (P.mixtureWeight lower upper : ℝ)), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

theorem mixtureWeight_mem_of_bracket (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (hlower : P.certificate.risk < P.solveRisk lower) (hupper : P.solveRisk upper ≤ P.certificate.risk) :
    0 ≤ P.mixtureWeight lower upper ∧ P.mixtureWeight lower upper ≤ 1 := by
  have hden : 0 < P.solveRisk lower - P.solveRisk upper := by linarith
  unfold mixtureWeight
  constructor
  · exact div_nonneg (sub_nonneg.mpr hupper) hden.le
  · apply (div_le_one hden).mpr
    linarith

theorem clippedMixtureWeight_eq (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (hzero : 0 ≤ P.mixtureWeight lower upper) (hone : P.mixtureWeight lower upper ≤ 1) :
    (P.clippedMixtureWeight lower upper).val = (P.mixtureWeight lower upper : ℝ) := by
  have hzeroReal : (0 : ℝ) ≤ P.mixtureWeight lower upper := by exact_mod_cast hzero
  have honeReal : (P.mixtureWeight lower upper : ℝ) ≤ 1 := by exact_mod_cast hone
  simp only [clippedMixtureWeight, min_eq_right honeReal, max_eq_right hzeroReal]

def stateWeight (P : PaperProofs.Paid.Parameters) : MultiplierState → Set.Icc (0 : ℝ) 1
  | .exact _ => ⟨0, by norm_num⟩
  | .bracket lower upper => P.clippedMixtureWeight lower upper

noncomputable def searchSeedLaw (P : PaperProofs.Paid.Parameters) (state : MultiplierState) : Measure P.SearchSeed :=
  (Statistics.BinarySymmetric.Parameters.rocCoinLaw (P.stateWeight state)).prod
    (menuSeedLaw P.certificate.stages P.tools)

instance searchSeedLaw_probability (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    IsProbabilityMeasure (P.searchSeedLaw state) := by
  unfold searchSeedLaw
  infer_instance

/-- The independent initial Bool chooses ONE WHOLE endpoint policy. Its
value is never updated or read from the visible history. -/
def stateRule (P : PaperProofs.Paid.Parameters) (state : MultiplierState) : PolicyRule P.sharedInstance P.SearchSeed :=
  fun seed history => match state with
  | .exact solution => P.solveRule solution seed.2 history
  | .bracket lower upper => if seed.1 then P.solveRule lower seed.2 history else P.solveRule upper seed.2 history

@[simp] theorem stateRule_bracket_true (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance)) :
    P.stateRule (.bracket lower upper) (true, seed) history = P.solveRule lower seed history := rfl

@[simp] theorem stateRule_bracket_false (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (seed : MenuSeed P.certificate.stages P.tools) (history : List (VisibleEvent P.sharedInstance)) :
    P.stateRule (.bracket lower upper) (false, seed) history = P.solveRule upper seed history := rfl

/-- A true initial selector follows the SAME complete endpoint path. No
success event or finite-cost condition is required for this identity. -/
theorem stateRule_bracket_run (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (choice : Bool)
    (seed : MenuSeed P.certificate.stages P.tools) (world : (P.input fee hfee).World) (n : ℕ) :
    run (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) ((choice, seed), world) n =
      run (P.input fee hfee) C.val mode accounting (P.solveRule (if choice then lower else upper)) (seed, world) n := by
  apply searchRun_seed_rule_eq
  intro history
  cases choice <;> rfl

theorem stateRule_bracket_bill (P : PaperProofs.Paid.Parameters) (lower upper : MultiplierSolve)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (choice : Bool)
    (seed : MenuSeed P.certificate.stages P.tools) (world : (P.input fee hfee).World) :
    runActualBill (P.input fee hfee) C.val mode accounting (P.stateRule (.bracket lower upper)) ((choice, seed), world) =
      runActualBill (P.input fee hfee) C.val mode accounting (P.solveRule (if choice then lower else upper)) (seed, world) := by
  apply searchBill_seed_rule_eq
  intro history
  cases choice <;> rfl

theorem stateRule_measurable (P : PaperProofs.Paid.Parameters) (state : MultiplierState) :
    MeasurableRule (P.stateRule state) := measurable_of_countable _

theorem stateRule_uncapped_legal (P : PaperProofs.Paid.Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    LegalRule (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) := by
  intro seed truth tapes n s hp hactive
  cases state with
  | exact solution =>
    have htransport := prefix_rule_transport (P.input fee hfee) C.val .uncapped accounting
      (P.stateRule (.exact solution)) (P.solveRule solution) seed seed.2 (fun _ => rfl) truth tapes hp
    exact P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools solution.table fee hfee C.val C.property.1.1
      accounting seed.2 truth tapes n s htransport hactive
  | bracket lower upper =>
    cases hbit : seed.1 with
    | false =>
      have hrule : ∀ history, P.stateRule (.bracket lower upper) seed history = P.solveRule upper seed.2 history := by
        intro history
        simp only [stateRule, hbit, Bool.false_eq_true, ite_false]
      have htransport := prefix_rule_transport (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule (.bracket lower upper)) (P.solveRule upper) seed seed.2 hrule truth tapes hp
      obtain ⟨next, step⟩ := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools upper.table fee hfee C.val C.property.1.1
        accounting seed.2 truth tapes n s htransport hactive
      exact ⟨next, (hrule s.history).symm ▸ step⟩
    | true =>
      have hrule : ∀ history, P.stateRule (.bracket lower upper) seed history = P.solveRule lower seed.2 history := by
        intro history
        simp only [stateRule, hbit, ite_true]
      have htransport := prefix_rule_transport (P.input fee hfee) C.val .uncapped accounting
        (P.stateRule (.bracket lower upper)) (P.solveRule lower) seed seed.2 hrule truth tapes hp
      obtain ⟨next, step⟩ := P.compiledMenuRule_uncapped_legal P.certificate.stages P.tools lower.table fee hfee C.val C.property.1.1
        accounting seed.2 truth tapes n s htransport hactive
      exact ⟨next, (hrule s.history).symm ▸ step⟩

def statePolicy (P : PaperProofs.Paid.Parameters) (state : MultiplierState)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting P.SearchSeed where
  rule := P.stateRule state
  measurable_rule := P.stateRule_measurable state
  legal := P.stateRule_uncapped_legal state fee hfee C accounting

def bisectMultiplier (P : PaperProofs.Paid.Parameters) (fee : ℚ) : MultiplierState → MultiplierState
  | .exact solution => .exact solution
  | .bracket lower upper =>
      let middle := P.solveMultiplier fee ((lower.multiplier + upper.multiplier) / 2)
      if P.solveRisk middle = P.certificate.risk then .exact middle
      else if P.certificate.risk < P.solveRisk middle then .bracket middle upper else .bracket lower middle

def searchStopped (P : PaperProofs.Paid.Parameters) (fee : ℚ) : MultiplierState → Bool
  | .exact _ => true
  | .bracket lower upper =>
      decide ((upper.multiplier - lower.multiplier) * P.certificate.risk ≤ P.mixtureCost fee lower upper / 2)

def multiplierStep (P : PaperProofs.Paid.Parameters) (fee : ℚ) (state : MultiplierState) : MultiplierState :=
  if P.searchStopped fee state then state else P.bisectMultiplier fee state

/-- Offline rational bisection, with the source's exact-risk and gap exits. -/
def multiplierSearch (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ → MultiplierState
  | 0 => P.initialMultiplierState fee
  | steps + 1 => P.multiplierStep fee (P.multiplierSearch fee steps)

/-- A t0-majority baseline keeps spending on failed paths and never pays
for a correction. Thus its all-path bill target is EXACTLY B. -/
def majorityCandidateRule (P : PaperProofs.Paid.Parameters) : PolicyRule P.sharedInstance Unit :=
  fun _ history =>
    if historyHalted history then .stop else
    if hstage : historyCursor history < P.certificate.stages then
      let stage : P.sharedInstance.Stage := ⟨historyCursor history, by simpa [sharedInstance] using hstage⟩
      match historyWrite history stage with
      | some _ => .advance stage
      | none =>
          let observations := historyObservations history stage
          if observations.all (fun symbol => symbol < 2) then
            if observations.length < P.certificate.t0 then .review stage
            else .write stage (decide (0 ≤ menuWordScore observations))
          else .abandon
    else if historyCursor history = P.certificate.stages then .stop else .abandon

def majorityRule (P : PaperProofs.Paid.Parameters) : PolicyRule P.sharedInstance Unit :=
  searchGuardRule P.majorityCandidateRule

def majorityPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting Unit where
  rule := P.majorityRule
  measurable_rule := measurable_of_countable _
  legal := searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting P.majorityCandidateRule

/-- The source's zero-charge blind policy: f=0 pays actual repairs up to K;
f>0 never executes a correction. The private m0 bits are the original fair
per-stage product seed, independent of World and of any mixture selector. -/
def zeroChargeCandidateRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    PolicyRule P.sharedInstance (MenuSeed P.certificate.stages P.tools) :=
  fun seed history =>
    if historyHalted history then .stop else
    if hstage : historyCursor history < P.certificate.stages then
      let stage : P.sharedInstance.Stage := ⟨historyCursor history, by simpa [sharedInstance] using hstage⟩
      match historyWrite history stage with
      | none => .write stage (seed stage)
      | some (bit, serial) => match historyReport history stage with
        | none => .abandon
        | some (truth, reportedSerial) =>
            if serial != reportedSerial then .abandon else
            if bit == truth then .advance stage else
            if fee = 0 then P.menuRepairAction P.certificate.stages P.tools history stage else .abandon
    else if historyCursor history = P.certificate.stages then .stop else .abandon

def zeroChargeRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    PolicyRule P.sharedInstance (MenuSeed P.certificate.stages P.tools) :=
  searchGuardRule (P.zeroChargeCandidateRule fee)

def zeroChargePolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting (MenuSeed P.certificate.stages P.tools) where
  rule := P.zeroChargeRule fee
  measurable_rule := measurable_of_countable _
  legal := searchGuardRule_uncapped_legal (P.input fee hfee) C.val C.property.1.1 accounting (P.zeroChargeCandidateRule fee)

/-- The exact rational Bin(N,1/2) upper tail, including every count K+1..N. -/
def blindBinomialTail (P : PaperProofs.Paid.Parameters) : ℚ :=
  ∑ mistakes ∈ Finset.range (P.certificate.stages + 1),
    if P.tools < mistakes then (Nat.choose P.certificate.stages mistakes : ℚ) * (1 / 2 : ℚ) ^ P.certificate.stages else 0

def zeroChargeRisk (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℚ :=
  if fee = 0 then P.blindBinomialTail else 1 - (1 / 2 : ℚ) ^ P.certificate.stages

def firstChargeFloor (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℚ :=
  if fee = 0 then P.reviewFee else min P.reviewFee fee

def positiveValueFloor (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℚ :=
  P.firstChargeFloor fee * (P.zeroChargeRisk fee - P.certificate.risk)

/-- The original J_bis, computed entirely by rational comparisons and
integer arithmetic. The real-log formula is proved separately below. -/
def bisectionBudget (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  Nat.clog 2 ⌈2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee⌉₊

theorem bisectionBudget_logb (P : PaperProofs.Paid.Parameters) (fee : ℚ)
    (hfloor : 0 < P.positiveValueFloor fee) :
    P.bisectionBudget fee =
      ⌈Real.logb 2 ((2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee : ℚ) : ℝ)⌉₊ := by
  apply Statistics.clog_ceil_rat_eq_natCeil_logb
  exact div_pos (mul_pos (mul_pos (by norm_num) P.Lambda_pos) P.certificate.risk_pos) hfloor

def idealSearchState (P : PaperProofs.Paid.Parameters) (fee : ℚ) : MultiplierState :=
  P.multiplierSearch fee (P.bisectionBudget fee)

/-- The actual source branch on delta>=zeta is chosen BEFORE the run. -/
def idealSearchRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) : PolicyRule P.sharedInstance P.SearchSeed :=
  if P.zeroChargeRisk fee ≤ P.certificate.risk then
    fun seed history => P.zeroChargeRule fee seed.2 history
  else P.stateRule (P.idealSearchState fee)

noncomputable def idealSearchSeedLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Measure P.SearchSeed :=
  if P.zeroChargeRisk fee ≤ P.certificate.risk then
    (Measure.dirac false).prod (menuSeedLaw P.certificate.stages P.tools)
  else P.searchSeedLaw (P.idealSearchState fee)

instance idealSearchSeedLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    IsProbabilityMeasure (P.idealSearchSeedLaw fee) := by
  unfold idealSearchSeedLaw
  split_ifs <;> infer_instance

theorem idealSearchRule_measurable (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    MeasurableRule (P.idealSearchRule fee) := measurable_of_countable _

theorem idealSearchRule_uncapped_legal (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    LegalRule (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) := by
  by_cases hzero : P.zeroChargeRisk fee ≤ P.certificate.risk
  · intro seed truth tapes n s hp hactive
    have hrule : ∀ history, P.idealSearchRule fee seed history = P.zeroChargeRule fee seed.2 history := by
      intro history
      simp only [idealSearchRule, ite_eq_left hzero]
    have htransport := prefix_rule_transport (P.input fee hfee) C.val .uncapped accounting
      (P.idealSearchRule fee) (P.zeroChargeRule fee) seed seed.2 hrule truth tapes hp
    obtain ⟨next, step⟩ := (P.zeroChargePolicy fee hfee C accounting).legal seed.2 truth tapes n s htransport hactive
    exact ⟨next, (hrule s.history).symm ▸ step⟩
  · simpa only [idealSearchRule, ite_eq_right hzero] using P.stateRule_uncapped_legal (P.idealSearchState fee) fee hfee C accounting

def idealSearchPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting P.SearchSeed where
  rule := P.idealSearchRule fee
  measurable_rule := P.idealSearchRule_measurable fee
  legal := P.idealSearchRule_uncapped_legal fee hfee C accounting

/-- Real actual operations of the old policy. Charges on an infinite or
eventually failed continuation are retained by runActualBill. -/
def isPositiveVariableAction (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Action P.sharedInstance → Bool
  | .review _ => true
  | .execute _ _ => decide (0 < fee)
  | _ => false

noncomputable def positiveChargeEvent (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type*} [MeasurableSpace Seed] (rule : PolicyRule P.sharedInstance Seed) :
    Set (Seed × (P.input fee hfee).World) :=
  {sample | ∃ n,
    let state := run (P.input fee hfee) C.val mode accounting rule sample n
    state.halted = false ∧ P.isPositiveVariableAction fee (rule sample.1 state.history) = true}

/-- Analysis assertions about the actual output, never table fields. -/
def SolveCorrect (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (solution : MultiplierSolve) : Prop :=
  solution.table = (P.solveMultiplier fee solution.multiplier).table ∧
  expectedBill (P.input fee hfee) C.val .uncapped accounting (P.solveRule solution)
      (menuSeedLaw P.certificate.stages P.tools) = ENNReal.ofReal (P.solveCost fee solution : ℝ) ∧
  risk (P.input fee hfee) C.val .uncapped accounting (P.solveRule solution)
      (menuSeedLaw P.certificate.stages P.tools) = ENNReal.ofReal (P.solveRisk solution : ℝ) ∧
  paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (solution.multiplier : ℝ)) =
    ENNReal.ofReal ((P.solveRecord solution).objective fee solution.multiplier : ℝ)

/-- D19, fixed t0-majority witness and the original Lambda initial bracket.
The majority bill B is paid on ALL paths, including every failed path. -/
def MajorityInitialBracket (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance),
    (∀ sample n, (run (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample n).ledger.executions = []) ∧
    (∀ sample, runActualBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule sample = ENNReal.ofReal (P.B : ℝ)) ∧
    expectedBill (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) = ENNReal.ofReal (P.B : ℝ) ∧
    risk (P.input fee hfee) C.val .uncapped accounting P.majorityRule (Measure.dirac ()) ≤ ENNReal.ofReal ((P.certificate.risk / 2 : ℚ) : ℝ) ∧
    let lower := P.solveMultiplier fee 0
    let upper := P.solveMultiplier fee P.Lambda
    P.SolveCorrect fee hfee C accounting lower ∧ P.SolveCorrect fee hfee C accounting upper ∧
    P.solveRisk lower = 1 ∧ P.solveCost fee lower = 0 ∧
    risk (P.input fee hfee) C.val .uncapped accounting (P.solveRule upper) (menuSeedLaw P.certificate.stages P.tools) ≤
      paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) / ENNReal.ofReal (P.Lambda : ℝ) ∧
    paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (P.Lambda : ℝ)) / ENNReal.ofReal (P.Lambda : ℝ) ≤
      ENNReal.ofReal (((P.B / P.Lambda) + P.certificate.risk / 2 : ℚ) : ℝ) ∧
    P.solveRisk upper ≤ 3 * P.certificate.risk / 4

def StateBracketCorrect (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) : MultiplierState → Prop
  | .exact solution =>
      P.SolveCorrect fee hfee C accounting solution ∧ 0 ≤ solution.multiplier ∧ solution.multiplier ≤ P.Lambda ∧
        P.solveRisk solution = P.certificate.risk
  | .bracket lower upper =>
      P.SolveCorrect fee hfee C accounting lower ∧ P.SolveCorrect fee hfee C accounting upper ∧
        0 ≤ lower.multiplier ∧ lower.multiplier < upper.multiplier ∧ upper.multiplier ≤ P.Lambda ∧
        P.certificate.risk < P.solveRisk lower ∧ P.solveRisk upper ≤ P.certificate.risk ∧
        0 ≤ P.solveRisk upper ∧ P.solveRisk lower ≤ 1 ∧
        0 ≤ P.solveCost fee lower ∧ 0 ≤ P.solveCost fee upper

/-- D20 is asserted for the REAL reachable search state, without assuming
its endpoint optimality, its bracket invariant, or its mixture law. -/
def ExactMixtureAndGap (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ),
    let state := P.multiplierSearch fee steps
    P.StateBracketCorrect fee hfee C accounting state ∧
    match state with
    | .exact solution =>
        risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) = P.targetRisk ∧
        expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) =
          ENNReal.ofReal (P.solveCost fee solution : ℝ) ∧
        ENNReal.ofReal (P.solveCost fee solution : ℝ) = P.uncappedValue C accounting fee hfee
    | .bracket lower upper =>
        let w := P.mixtureWeight lower upper
        let U := P.mixtureCost fee lower upper
        let L := P.mixtureLower fee upper
        0 ≤ w ∧ w ≤ 1 ∧ (P.clippedMixtureWeight lower upper).val = (w : ℝ) ∧
        risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) = P.targetRisk ∧
        expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) = ENNReal.ofReal (U : ℝ) ∧
        -upper.multiplier ≤ (P.solveCost fee lower - P.solveCost fee upper) / (P.solveRisk lower - P.solveRisk upper) ∧
        (P.solveCost fee lower - P.solveCost fee upper) / (P.solveRisk lower - P.solveRisk upper) ≤ -lower.multiplier ∧
        0 ≤ U - L ∧ U - L ≤ (upper.multiplier - lower.multiplier) * (P.certificate.risk - P.solveRisk upper) ∧
        (upper.multiplier - lower.multiplier) * (P.certificate.risk - P.solveRisk upper) ≤
          (upper.multiplier - lower.multiplier) * P.certificate.risk ∧
        ENNReal.ofReal (L : ℝ) ≤ P.uncappedValue C accounting fee hfee ∧
        P.uncappedValue C accounting fee hfee ≤ ENNReal.ofReal (U : ℝ)

/-- D21's stopping implication for this fixed whole-policy mixture.
It compares to the original full-policy cap-relaxed value, not a recurrence. -/
def StoppedTwoFactor (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) (steps : ℕ),
    let state := P.multiplierSearch fee steps
    P.searchStopped fee state = true →
      risk (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) = P.targetRisk ∧
      expectedBill (P.input fee hfee) C.val .uncapped accounting (P.stateRule state) (P.searchSeedLaw state) ≤
        2 * P.uncappedValue C accounting fee hfee

/-- Original cap arithmetic PLUS the H0 bound of THIS blind script only.
Risk, price, ET and success are not qualification fields. -/
def ZeroChargeOriginalQualification (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) : Prop :=
  P.NativeCapQualification C ∧
    ∀ sample n, (run (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample n).ledger.normalCalls ≤
      (C.val.normalCallBound : ℕ∞)

/-- D22 exact zero-charge optimum. Its lower side includes all private
seeds, histories, non-MAP decisions, abandonment and infinite-ET policies. -/
def ZeroChargeOptimum (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance),
    (∀ sample, runActualBill (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) sample = 0) ∧
    risk (P.input fee hfee) C.val .uncapped accounting (P.zeroChargeRule fee) (menuSeedLaw P.certificate.stages P.tools) =
      ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) ∧
    (∀ (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
          expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν = 0 →
            ENNReal.ofReal (P.zeroChargeRisk fee : ℝ) ≤ risk (P.input fee hfee) C.val mode accounting policy.rule ν) ∧
    (P.ZeroChargeOriginalQualification fee hfee C accounting →
      ∃ policy : Policy (P.input fee hfee) C.val .native accounting (MenuSeed P.certificate.stages P.tools),
        policy.rule = P.zeroChargeRule fee ∧
        expectedBill (P.input fee hfee) C.val .native accounting policy.rule (menuSeedLaw P.certificate.stages P.tools) = 0 ∧
        risk (P.input fee hfee) C.val .native accounting policy.rule (menuSeedLaw P.certificate.stages P.tools) =
          ENNReal.ofReal (P.zeroChargeRisk fee : ℝ))

/-- D22's first-positive-charge event and the exact positive lower amount.
All ENNReal charges remain extended; no finiteness premise or toReal occurs. -/
def PositiveChargeLower (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee), P.certificate.risk < P.zeroChargeRisk fee →
    0 < P.positiveValueFloor fee ∧
    ∀ (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
      (mode : ResourceMode) (Seed : Type u) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ policy : Policy (P.input fee hfee) C.val mode accounting Seed,
          risk (P.input fee hfee) C.val mode accounting policy.rule ν ≤ P.targetRisk →
            ENNReal.ofReal ((P.zeroChargeRisk fee - P.certificate.risk : ℚ) : ℝ) ≤
              (P.input fee hfee).seededWorldLaw ν (P.positiveChargeEvent fee hfee C mode accounting policy.rule) ∧
            (∀ sample ∈ P.positiveChargeEvent fee hfee C mode accounting policy.rule,
              ENNReal.ofReal (P.firstChargeFloor fee : ℝ) ≤
                runActualBill (P.input fee hfee) C.val mode accounting policy.rule sample) ∧
            ENNReal.ofReal (P.positiveValueFloor fee : ℝ) ≤
              expectedBill (P.input fee hfee) C.val mode accounting policy.rule ν

/-- D22 finite termination of the actual offline search. The endpoint
backend remains uncapped; the zero-charge exit alone has a native target. -/
def FiniteMultiplierTermination (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance),
    (P.zeroChargeRisk fee ≤ P.certificate.risk →
      expectedBill (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) = 0 ∧
      risk (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) ≤ P.targetRisk) ∧
    (P.certificate.risk < P.zeroChargeRisk fee →
      P.searchStopped fee (P.idealSearchState fee) = true ∧
      ENNReal.ofReal (P.positiveValueFloor fee : ℝ) ≤ P.uncappedValue C accounting fee hfee ∧
      risk (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) = P.targetRisk ∧
      expectedBill (P.input fee hfee) C.val .uncapped accounting (P.idealSearchRule fee) (P.idealSearchSeedLaw fee) ≤
        2 * P.uncappedValue C accounting fee hfee)

def MultiplierSearchClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.MajorityInitialBracket ∧ P.ExactMixtureAndGap ∧ P.StoppedTwoFactor ∧
    P.ZeroChargeOptimum.{u} ∧ P.PositiveChargeLower.{u} ∧ P.FiniteMultiplierTermination

end Parameters
end PaperProofs.Paid
