module

public import PaperProofs.Paid.CalibratedBackend
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Log

/-! A fixed cached frontend for the already fixed paid algorithm.
No RAM time is inferred from extensional equality or loop-label counts.
The frontend stores endpoint constants and calibration errors/weights.
Each calibration Q-row is let-bound once as a temporary value.
All rule/seed-law equivalences below are separate from the
pending statistical performance claims of the old modules. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.Parameters

open Common Common.Native Statistics

structure EndpointConstant where
  error : ℚ
  charge : ℚ
  deriving DecidableEq, Repr

def endpointConstant (P : PaperProofs.Paid.Parameters) (m : ℕ) : EndpointConstant :=
  ⟨P.binarySymmetric.endpointError m, P.binarySymmetric.endpointCharge m⟩

def endpointCache (P : PaperProofs.Paid.Parameters) : Array EndpointConstant :=
  Array.ofFn (fun m : Fin (P.certificate.M + 1) => P.endpointConstant m.val)

/-- The fallback is only evaluated OUTSIDE the stored menu. Every valid
testing index reads the stored endpoint, without recomputing its powers;
no host runtime, allocation, or copying theorem is asserted here. -/
def cachedEndpoint (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (m : ℕ) : EndpointConstant :=
  if h : m < cache.size then cache[m] else P.endpointConstant m

@[simp] theorem cachedEndpoint_eq (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.cachedEndpoint P.endpointCache m = P.endpointConstant m := by
  unfold cachedEndpoint
  split_ifs with h
  · simp only [endpointCache, Array.getElem_ofFn]
  · rfl

def cachedMenuTestingEntry (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee penalty : ℚ)
    (previous : MenuRow) (tools level : ℕ) : MenuEntry :=
  let good := previous.getD tools abandonEntry
  let bad := P.menuBadBranch fee penalty previous tools
  let endpoint := P.cachedEndpoint cache level
  {
    action := .test level bad.1
    observation := endpoint.charge + (1 - endpoint.error) * good.observation + endpoint.error * bad.2.observation
    repairs := (1 - endpoint.error) * good.repairs + endpoint.error * bad.2.repairs
    failure := (1 - endpoint.error) * good.failure + endpoint.error * bad.2.failure }

@[simp] theorem cachedMenuTestingEntry_eq (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools level : ℕ) :
    P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level =
      P.menuTestingEntry fee penalty previous tools level := by
  simp only [cachedMenuTestingEntry, cachedEndpoint_eq, endpointConstant, menuTestingEntry]

def cachedLeastTestingLevel (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : ℕ :=
  ((List.range (P.certificate.M + 1)).argmin
    (fun level => (P.cachedMenuTestingEntry cache fee penalty previous tools level).objective fee penalty)).getD 0

@[simp] theorem cachedLeastTestingLevel_eq (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    P.cachedLeastTestingLevel P.endpointCache fee penalty previous tools = P.leastTestingLevel fee penalty previous tools := by
  simp only [cachedLeastTestingLevel, cachedMenuTestingEntry_eq, leastTestingLevel]

def cachedNextMenuEntry (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : MenuEntry :=
  if penalty = 0 then abandonEntry else
  let best := P.cachedMenuTestingEntry cache fee penalty previous tools (P.cachedLeastTestingLevel cache fee penalty previous tools)
  if penalty ≤ best.objective fee penalty then abandonEntry else best

@[simp] theorem cachedNextMenuEntry_eq (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    P.cachedNextMenuEntry P.endpointCache fee penalty previous tools = P.nextMenuEntry fee penalty previous tools := by
  simp only [cachedNextMenuEntry, cachedLeastTestingLevel_eq, cachedMenuTestingEntry_eq, nextMenuEntry]

def cachedNextMenuRow (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) : MenuRow :=
  Array.ofFn (fun k : Fin (tools + 1) => P.cachedNextMenuEntry cache fee penalty previous k.val)

@[simp] theorem cachedNextMenuRow_eq (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    P.cachedNextMenuRow P.endpointCache fee penalty previous tools = P.nextMenuRow fee penalty previous tools := by
  simp only [cachedNextMenuRow, cachedNextMenuEntry_eq, nextMenuRow]

def cachedSolveMenuTable (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee penalty : ℚ)
    (tools : ℕ) : ℕ → MenuTable
  | 0 => #[baseMenuRow tools]
  | stages + 1 =>
      let rows := P.cachedSolveMenuTable cache fee penalty tools stages
      rows.push (P.cachedNextMenuRow cache fee penalty (rows.getD stages (baseMenuRow tools)) tools)

@[simp] theorem cachedSolveMenuTable_eq (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    P.cachedSolveMenuTable P.endpointCache fee penalty tools stages = P.solveMenuTable fee penalty tools stages := by
  induction stages with
  | zero => rfl
  | succ stages ih => simp only [cachedSolveMenuTable, ih, cachedNextMenuRow_eq, solveMenuTable]

def cachedSolveMultiplier (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee multiplier : ℚ) : MultiplierSolve :=
  ⟨multiplier, P.cachedSolveMenuTable cache fee multiplier P.tools P.certificate.stages⟩

@[simp] theorem cachedSolveMultiplier_eq (P : PaperProofs.Paid.Parameters) (fee multiplier : ℚ) :
    P.cachedSolveMultiplier P.endpointCache fee multiplier = P.solveMultiplier fee multiplier := by
  simp only [cachedSolveMultiplier, cachedSolveMenuTable_eq, solveMultiplier]

def cachedInitialState (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) : MultiplierState :=
  .bracket (P.cachedSolveMultiplier cache fee 0) (P.cachedSolveMultiplier cache fee P.Lambda)

def cachedBisect (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) : MultiplierState → MultiplierState
  | .exact solution => .exact solution
  | .bracket lower upper =>
      let middle := P.cachedSolveMultiplier cache fee ((lower.multiplier + upper.multiplier) / 2)
      if P.solveRisk middle = P.certificate.risk then .exact middle
      else if P.certificate.risk < P.solveRisk middle then .bracket middle upper else .bracket lower middle

def cachedMultiplierStep (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ)
    (state : MultiplierState) : MultiplierState :=
  if P.searchStopped fee state then state else P.cachedBisect cache fee state

@[simp] theorem cachedMultiplierStep_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (state : MultiplierState) :
    P.cachedMultiplierStep P.endpointCache fee state = P.multiplierStep fee state := by
  cases state <;> simp only [cachedMultiplierStep, cachedBisect, cachedSolveMultiplier_eq, multiplierStep, bisectMultiplier]

def cachedMultiplierSearch (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) : ℕ → MultiplierState
  | 0 => P.cachedInitialState cache fee
  | steps + 1 => P.cachedMultiplierStep cache fee (P.cachedMultiplierSearch cache fee steps)

@[simp] theorem cachedMultiplierSearch_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (steps : ℕ) :
    P.cachedMultiplierSearch P.endpointCache fee steps = P.multiplierSearch fee steps := by
  induction steps with
  | zero => simp only [cachedMultiplierSearch, cachedInitialState, cachedSolveMultiplier_eq,
      multiplierSearch, initialMultiplierState]
  | succ steps ih => simp only [cachedMultiplierSearch, ih, cachedMultiplierStep_eq, multiplierSearch]

/-- The Q-row is let-bound ONCE before summing its terminal losses. -/
def cachedCappedError (P : PaperProofs.Paid.Parameters) (m : ℕ) : ℚ :=
  let finalRow := P.walkRow (m + 1) true P.certificate.Q
  ∑ state : WalkCell (m + 1), finalRow.getD state.val 0 *
    if state.val < m + 1 then 1 else if state.val = m + 1 then 1 / 2 else 0

@[simp] theorem cachedCappedError_eq (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.cachedCappedError m = P.cappedError m := rfl

structure CalibrationConstant where
  error : ℚ
  weight : ℚ
  deriving DecidableEq, Repr

def calibrationWeightCache (P : PaperProofs.Paid.Parameters) (endpoints : Array EndpointConstant) : Array CalibrationConstant :=
  Array.ofFn (fun m : Fin (P.certificate.M + 1) =>
    let q := P.cachedCappedError m.val
    ⟨q, (1 / 2 - (P.cachedEndpoint endpoints m.val).error) / (1 / 2 - q)⟩)

def cachedCalibrationWeight (P : PaperProofs.Paid.Parameters) (cache : Array CalibrationConstant) (m : ℕ) : ℚ :=
  if h : m < cache.size then cache[m].weight else P.calibrationWeight m

def cachedCalibrationError (P : PaperProofs.Paid.Parameters) (cache : Array CalibrationConstant) (m : ℕ) : ℚ :=
  if h : m < cache.size then cache[m].error else P.cappedError m

@[simp] theorem cachedCalibrationError_eq (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.cachedCalibrationError (P.calibrationWeightCache P.endpointCache) m = P.cappedError m := by
  unfold cachedCalibrationError
  split_ifs with h
  · simp only [calibrationWeightCache, Array.getElem_ofFn, cachedCappedError_eq]
  · rfl

@[simp] theorem cachedCalibrationWeight_eq (P : PaperProofs.Paid.Parameters) (m : ℕ) :
    P.cachedCalibrationWeight (P.calibrationWeightCache P.endpointCache) m = P.calibrationWeight m := by
  unfold cachedCalibrationWeight
  split_ifs with h
  · simp only [calibrationWeightCache, Array.getElem_ofFn, cachedEndpoint_eq, endpointConstant,
      cachedCappedError_eq, calibrationWeight]
  · rfl

structure CachedFrontend where
  endpoints : Array EndpointConstant
  calibrationWeights : Array CalibrationConstant
  state : MultiplierState

def buildCachedFrontend (P : PaperProofs.Paid.Parameters) (fee : ℚ) : CachedFrontend :=
  let endpoints := P.endpointCache
  let calibration := P.calibrationWeightCache endpoints
  let state := P.cachedMultiplierSearch endpoints fee (P.bisectionBudget fee)
  ⟨endpoints, calibration, state⟩

@[simp] theorem buildCachedFrontend_state (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    (P.buildCachedFrontend fee).state = P.idealSearchState fee :=
  P.cachedMultiplierSearch_eq fee (P.bisectionBudget fee)

def cachedRuleFrom (P : PaperProofs.Paid.Parameters) (fee : ℚ) (frontend : CachedFrontend) :
    PolicyRule P.sharedInstance P.CalibratedSearchSeed :=
  searchGuardRule (if P.zeroChargeRisk fee ≤ P.certificate.risk then
    fun seed history => P.zeroChargeCandidateRule fee seed.2.1 history
    else P.calibratedStateCandidate frontend.state)

def cachedAlgorithmRule (P : PaperProofs.Paid.Parameters) (fee : ℚ) : PolicyRule P.sharedInstance P.CalibratedSearchSeed :=
  P.cachedRuleFrom fee (P.buildCachedFrontend fee)

@[simp] theorem cachedAlgorithmRule_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    P.cachedAlgorithmRule fee = P.calibratedAlgorithmRule fee := by
  simp only [cachedAlgorithmRule, cachedRuleFrom, buildCachedFrontend_state, calibratedAlgorithmRule, calibratedAlgorithmCandidate]

def cachedClippedWeight (P : PaperProofs.Paid.Parameters) (frontend : CachedFrontend) (m : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (P.cachedCalibrationWeight frontend.calibrationWeights m : ℝ)), le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

@[simp] theorem cachedClippedWeight_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (m : ℕ) :
    P.cachedClippedWeight (P.buildCachedFrontend fee) m = P.clippedCalibrationWeight m := by
  apply Subtype.ext
  simp only [cachedClippedWeight, buildCachedFrontend, cachedCalibrationWeight_eq, clippedCalibrationWeight]

noncomputable def cachedSeedLawFrom (P : PaperProofs.Paid.Parameters) (fee : ℚ) (frontend : CachedFrontend) : Measure P.CalibratedSearchSeed :=
  let marks : Measure P.CalibrationMarks := Measure.pi fun _stage =>
    Measure.pi fun level : Fin (P.certificate.M + 1) =>
      BinarySymmetric.Parameters.rocCoinLaw (P.cachedClippedWeight frontend level.val)
  let seedLaw := (menuSeedLaw P.certificate.stages P.tools).prod marks
  if P.zeroChargeRisk fee ≤ P.certificate.risk then (Measure.dirac false).prod seedLaw
  else (BinarySymmetric.Parameters.rocCoinLaw (P.stateWeight frontend.state)).prod seedLaw

noncomputable def cachedAlgorithmSeedLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Measure P.CalibratedSearchSeed :=
  P.cachedSeedLawFrom fee (P.buildCachedFrontend fee)

@[simp] theorem cachedAlgorithmSeedLaw_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    P.cachedAlgorithmSeedLaw fee = P.calibratedAlgorithmSeedLaw fee := by
  simp only [cachedAlgorithmSeedLaw, cachedSeedLawFrom, cachedClippedWeight_eq, buildCachedFrontend_state,
    calibratedAlgorithmSeedLaw, calibratedStateSeedLaw, calibratedMenuSeedLaw, calibrationMarksLaw]

/-- A single preparation stores both caches and the chosen table state.
The rule and seed-law readers share THIS frontend value. -/
noncomputable def cachedProgram (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    CachedFrontend × PolicyRule P.sharedInstance P.CalibratedSearchSeed × Measure P.CalibratedSearchSeed :=
  let frontend := P.buildCachedFrontend fee
  (frontend, P.cachedRuleFrom fee frontend, P.cachedSeedLawFrom fee frontend)

@[simp] theorem cachedProgram_rule_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    (P.cachedProgram fee).2.1 = P.calibratedAlgorithmRule fee := P.cachedAlgorithmRule_eq fee

@[simp] theorem cachedProgram_seedLaw_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    (P.cachedProgram fee).2.2 = P.calibratedAlgorithmSeedLaw fee := P.cachedAlgorithmSeedLaw_eq fee

def cachedAlgorithmPolicy (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    Policy (P.input fee hfee) C.val .uncapped accounting P.CalibratedSearchSeed where
  rule := P.cachedAlgorithmRule fee
  measurable_rule := by
    rw [cachedAlgorithmRule_eq]
    exact (P.calibratedAlgorithmPolicy fee hfee C accounting).measurable_rule
  legal := by
    rw [cachedAlgorithmRule_eq]
    exact (P.calibratedAlgorithmPolicy fee hfee C accounting).legal

theorem cachedProgram_run_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (sample : P.CalibratedSearchSeed × (P.input fee hfee).World) (n : ℕ) :
    run (P.input fee hfee) C.val mode accounting (P.cachedProgram fee).2.1 sample n =
      run (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee) sample n := by
  rw [cachedProgram_rule_eq]

theorem cachedProgram_risk_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) :
    risk (P.input fee hfee) C.val mode accounting (P.cachedProgram fee).2.1 (P.cachedProgram fee).2.2 =
      risk (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmSeedLaw fee) := by
  rw [cachedProgram_rule_eq, cachedProgram_seedLaw_eq]

theorem cachedProgram_expectedBill_eq (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) :
    expectedBill (P.input fee hfee) C.val mode accounting (P.cachedProgram fee).2.1 (P.cachedProgram fee).2.2 =
      expectedBill (P.input fee hfee) C.val mode accounting (P.calibratedAlgorithmRule fee) (P.calibratedAlgorithmSeedLaw fee) := by
  rw [cachedProgram_rule_eq, cachedProgram_seedLaw_eq]

def CachedOriginalQualification (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) : Prop :=
  P.NativeCapQualification C ∧ NormalCallCertificate (P.input fee hfee) C.val .uncapped accounting
    (P.cachedAlgorithmPolicy fee hfee C accounting) C.val.normalCallBound

theorem cachedOriginalQualification_iff (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance) :
    P.CachedOriginalQualification fee hfee C accounting ↔ P.CalibratedOriginalQualification fee hfee C accounting := by
  simp only [CachedOriginalQualification, CalibratedOriginalQualification, NormalCallCertificate,
    cachedAlgorithmPolicy, calibratedAlgorithmPolicy, cachedAlgorithmRule_eq]

/-- Number of ACTUALLY stored MenuEntry records, not allocated bytes or
peak live RAM. The array data themselves are the counted object. -/
def tableCellCount (table : MenuTable) : ℕ := (table.toList.map Array.size).sum

theorem solveMenuTable_cellCount (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    tableCellCount (P.solveMenuTable fee penalty tools stages) = (stages + 1) * (tools + 1) := by
  induction stages with
  | zero => simp [tableCellCount, solveMenuTable, baseMenuRow]
  | succ stages ih =>
    simp only [solveMenuTable, tableCellCount, Array.toList_push, List.map_append,
      List.map_singleton, List.sum_append, List.sum_singleton, nextMenuRow_size]
    change tableCellCount (P.solveMenuTable fee penalty tools stages) + (tools + 1) = _
    rw [ih]
    ring

theorem cachedSolveMenuTable_cellCount (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (tools stages : ℕ) :
    tableCellCount (P.cachedSolveMenuTable P.endpointCache fee penalty tools stages) = (stages + 1) * (tools + 1) := by
  rw [cachedSolveMenuTable_eq, P.solveMenuTable_cellCount]

@[simp] theorem endpointCache_size (P : PaperProofs.Paid.Parameters) : P.endpointCache.size = P.certificate.M + 1 := by
  simp only [endpointCache, Array.size_ofFn]

@[simp] theorem calibrationWeightCache_size (P : PaperProofs.Paid.Parameters) (endpoints : Array EndpointConstant) :
    (P.calibrationWeightCache endpoints).size = P.certificate.M + 1 := by
  simp only [calibrationWeightCache, Array.size_ofFn]

/-- The exact additional solve request in the source branch. This is a
solve-invocation log, not a count of all rational operations. -/
def nextSolveRequests (P : PaperProofs.Paid.Parameters) (fee : ℚ) (state : MultiplierState) : List ℚ :=
  if P.searchStopped fee state then [] else match state with
  | .exact _ => []
  | .bracket lower upper => [(lower.multiplier + upper.multiplier) / 2]

theorem nextSolveRequests_length_le (P : PaperProofs.Paid.Parameters) (fee : ℚ) (state : MultiplierState) :
    (P.nextSolveRequests fee state).length ≤ 1 := by
  cases state <;> unfold nextSolveRequests <;> split_ifs <;> simp

/-- Joint execution of the actual cached search state and its source-level
solve log, with no recomputation of earlier search states by the logger. -/
def cachedSearchWithLog (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) :
    ℕ → MultiplierState × List ℚ
  | 0 => (P.cachedInitialState cache fee, [0, P.Lambda])
  | steps + 1 =>
      let previous := P.cachedSearchWithLog cache fee steps
      (P.cachedMultiplierStep cache fee previous.1, previous.2 ++ P.nextSolveRequests fee previous.1)

theorem cachedSearchWithLog_state (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) (steps : ℕ) :
    (P.cachedSearchWithLog cache fee steps).1 = P.cachedMultiplierSearch cache fee steps := by
  induction steps with
  | zero => rfl
  | succ steps ih => simp only [cachedSearchWithLog, ih, cachedMultiplierSearch]

theorem cachedSearchWithLog_solve_count (P : PaperProofs.Paid.Parameters) (cache : Array EndpointConstant) (fee : ℚ) (steps : ℕ) :
    (P.cachedSearchWithLog cache fee steps).2.length ≤ steps + 2 := by
  induction steps with
  | zero => simp only [cachedSearchWithLog, List.length_cons, List.length_nil, Nat.zero_add, le_refl]
  | succ steps ih =>
    have h := P.nextSolveRequests_length_le fee (P.cachedSearchWithLog cache fee steps).1
    simp only [cachedSearchWithLog, List.length_append]
    omega

theorem cachedSearchWithLog_bisection_count (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2.length ≤ P.bisectionBudget fee + 2 :=
  P.cachedSearchWithLog_solve_count P.endpointCache fee (P.bisectionBudget fee)

/-- Labels of the literal state/letter iterations in walkUpdate. They
count array mass updates, not host Array copies, bit operations, or RAM time. -/
def walkUpdateLabels (level : ℕ) : List (ℕ × ℕ) :=
  (List.finRange (2 * level + 1)).flatMap (fun state =>
    (List.finRange 2).map (fun letter => (state.val, letter.val)))

theorem walkUpdateLabels_length (level : ℕ) : (walkUpdateLabels level).length = 2 * (2 * level + 1) := by
  simp [walkUpdateLabels, List.length_flatMap, Nat.mul_comm]

def walkRowLabels (level steps : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range steps).flatMap (fun clock => (walkUpdateLabels level).map (fun label => (clock, label)))

theorem walkRowLabels_length (level steps : ℕ) : (walkRowLabels level steps).length = 2 * steps * (2 * level + 1) := by
  simp [walkRowLabels, List.length_flatMap, walkUpdateLabels_length, Nat.mul_comm, Nat.mul_left_comm]

def calibrationUpdateLabels (levels quota : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range levels).flatMap (fun m => (walkRowLabels (m + 1) quota).map (fun label => (m, label)))

theorem calibrationUpdateLabels_length (levels quota : ℕ) :
    (calibrationUpdateLabels levels quota).length = 2 * quota * levels * (levels + 2) := by
  induction levels with
  | zero => simp [calibrationUpdateLabels]
  | succ levels ih =>
    have hstep : calibrationUpdateLabels (levels + 1) quota = calibrationUpdateLabels levels quota ++
        (walkRowLabels (levels + 1) quota).map (fun label => (levels, label)) := by
      simp only [calibrationUpdateLabels, List.range_succ, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hstep, List.length_append, ih, List.length_map, walkRowLabels_length]
    ring

theorem calibrationUpdateLabels_bound (P : PaperProofs.Paid.Parameters) :
    (calibrationUpdateLabels (P.certificate.M + 1) P.certificate.Q).length ≤
      6 * P.certificate.Q * (P.certificate.M + 1)^2 := by
  rw [calibrationUpdateLabels_length]
  have h : P.certificate.M + 1 + 2 ≤ 3 * (P.certificate.M + 1) := by omega
  calc
    _ ≤ 2 * P.certificate.Q * (P.certificate.M + 1) * (3 * (P.certificate.M + 1)) := Nat.mul_le_mul_left _ h
    _ = _ := by ring

/-- Standard binary length, with one bit allotted to zero. These are
encoding sizes of concrete rationals, not a claim about Lean object layout. -/
def natBits (n : ℕ) : ℕ := Nat.log2 n + 1

def ratDenBits (q : ℚ) : ℕ := natBits q.den
def ratNumBits (q : ℚ) : ℕ := natBits q.num.natAbs
def ratEncodingBits (q : ℚ) : ℕ := 1 + ratNumBits q + ratDenBits q

def menuScalars (P : PaperProofs.Paid.Parameters) (fee : ℚ) : List ℚ :=
  P.endpointCache.toList.flatMap (fun endpoint => [endpoint.error, endpoint.charge]) ++ [P.reviewFee, fee]

def menuCommonDenominator (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  ((P.menuScalars fee).map Rat.den).prod

def MenuEncodingBound (P : PaperProofs.Paid.Parameters) (fee : ℚ) (L : ℕ) : Prop :=
  1 ≤ L ∧ ∀ scalar ∈ P.menuScalars fee, ratEncodingBits scalar ≤ L

/-- Original D:623--627, with the actual cached table fields and the
explicit common denominator. Multiplier bits enter objective records;
there is no assumption of endpoint optimality or a policy-cost bound. -/
def MenuBitClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee penalty : ℚ) (L : ℕ), P.MenuEncodingBound fee L →
    natBits (P.menuCommonDenominator fee) ≤ (2 * (P.certificate.M + 1) + 2) * L ∧
    ∀ n : ℕ, n ≤ P.certificate.stages → ∀ k : ℕ, k ≤ P.tools →
      let entry := menuEntryAt (P.cachedSolveMenuTable P.endpointCache fee penalty P.tools P.certificate.stages) n k
      entry.observation.den ∣ (P.menuCommonDenominator fee)^n ∧
      entry.repairs.den ∣ (P.menuCommonDenominator fee)^n ∧
      entry.failure.den ∣ (P.menuCommonDenominator fee)^n ∧
      (entry.objective fee penalty).den ∣ (P.menuCommonDenominator fee)^(n + 1) * penalty.den ∧
      ratDenBits entry.observation ≤ (n + 1) * (2 * (P.certificate.M + 1) + 2) * L ∧
      ratDenBits entry.repairs ≤ (n + 1) * (2 * (P.certificate.M + 1) + 2) * L ∧
      ratDenBits entry.failure ≤ (n + 1) * (2 * (P.certificate.M + 1) + 2) * L ∧
      ratDenBits (entry.objective fee penalty) ≤ (n + 1) * (2 * (P.certificate.M + 1) + 2) * L + ratDenBits penalty ∧
      (∀ scalar ∈ [entry.observation, entry.repairs, entry.failure, entry.objective fee penalty],
        ratNumBits scalar ≤ ratDenBits scalar + natBits (⌈|scalar|⌉₊ + 1) +
          natBits P.certificate.stages + natBits P.tools + 2)

/-- A common denominator for BOTH rational BSC letters. The public
gamma, not any sampled hidden bit, determines this constant. -/
def channelCommonDenominator (P : PaperProofs.Paid.Parameters) : ℕ := 2 * P.certificate.gamma.den

/-- Original D:628--629. Exact q_m/omega_m values are those in the
independent array cache. The fixed Q dominates the endpoint levels; no
new asymptotic relation or successful-path restriction is a premise. -/
def CalibrationBitClaims : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (P : PaperProofs.Paid.Parameters) (Lgamma : ℕ), ratEncodingBits P.certificate.gamma ≤ Lgamma →
    ∀ m : ℕ, m ≤ P.certificate.M →
      (P.cachedCappedError m).den ∣ 2 * P.channelCommonDenominator^P.certificate.Q ∧
      ratDenBits (P.cachedCappedError m) ≤ C * (P.certificate.Q + 1) * (Lgamma + 2) ∧
      ratDenBits (P.cachedCalibrationWeight (P.calibrationWeightCache P.endpointCache) m) ≤
        C * (P.certificate.Q + 1) * (Lgamma + 2) ∧
      ratEncodingBits (P.cachedCalibrationWeight (P.calibrationWeightCache P.endpointCache) m) ≤
        C * (P.certificate.Q + 1) * (Lgamma + 2)

/-- Original D:629--631: division by the difference of the two ACTUAL
rational endpoint risks has a linear encoding-size bound in its operands,
including their numerators. It does not create an exponential bit tree. -/
def MixtureBitClaims : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ) (lower upper : MultiplierSolve),
    ratEncodingBits (P.mixtureWeight lower upper) ≤
      C * (ratEncodingBits P.certificate.risk + ratEncodingBits (P.solveRisk lower) +
        ratEncodingBits (P.solveRisk upper) + 1) ∧
    ratEncodingBits (P.mixtureCost fee lower upper) ≤
      C * (ratEncodingBits (P.mixtureWeight lower upper) + ratEncodingBits (P.solveCost fee lower) +
        ratEncodingBits (P.solveCost fee upper) + 1)

/-- Original D:633--636. Tiny positive f is counted by its own full
rational encoding; neither f nor zeta_f-delta is treated as a unit-cost oracle. -/
def PositiveGapBitClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  ∀ (fee : ℚ), 0 ≤ fee →
    ratEncodingBits (P.firstChargeFloor fee) ≤ ratEncodingBits P.reviewFee + ratEncodingBits fee ∧
    (P.certificate.risk < P.zeroChargeRisk fee →
      1 / ((2 : ℚ)^P.certificate.stages * (P.certificate.risk.den : ℚ)) ≤
        P.zeroChargeRisk fee - P.certificate.risk ∧
      Real.log (((P.zeroChargeRisk fee - P.certificate.risk : ℚ) : ℝ)⁻¹) ≤
        (P.certificate.stages : ℝ) * Real.log 2 + Real.log (P.certificate.risk.den : ℝ))

def menuActionBits : MenuAction → ℕ
  | .finish | .abandon => 2
  | .test level _ => 3 + natBits level

def menuEntryBits (entry : MenuEntry) : ℕ := menuActionBits entry.action +
  ratEncodingBits entry.observation + ratEncodingBits entry.repairs + ratEncodingBits entry.failure

def menuTableBits (table : MenuTable) : ℕ :=
  (table.toList.map (fun row => (row.toList.map menuEntryBits).sum)).sum

def solveBits (solution : MultiplierSolve) : ℕ := ratEncodingBits solution.multiplier + menuTableBits solution.table

def stateBits : MultiplierState → ℕ
  | .exact solution => 1 + solveBits solution
  | .bracket lower upper => 1 + solveBits lower + solveBits upper

def frontendBits (frontend : CachedFrontend) : ℕ :=
  (frontend.endpoints.toList.map (fun endpoint => ratEncodingBits endpoint.error + ratEncodingBits endpoint.charge)).sum +
    (frontend.calibrationWeights.toList.map (fun calibration => ratEncodingBits calibration.error + ratEncodingBits calibration.weight)).sum +
      stateBits frontend.state

def numericalSize (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  P.certificate.t0 + P.certificate.M + P.certificate.Q + P.bisectionBudget fee + frontendBits (P.buildCachedFrontend fee)

/-- The data-size part of D:637--640. These are exact polynomial targets
for the existing fixed functions, not an existential replacement program.
No claim about RAM/bit running time or a private-coin sampler is included. -/
def FixedGammaPolynomialData (gamma : ℚ) : Prop :=
  ∃ C degree : ℕ, 0 < C ∧ ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ),
    P.certificate.gamma = gamma → 0 ≤ fee →
      P.numericalSize fee ≤ C * (P.certificate.stages + ratEncodingBits P.certificate.risk +
        ratEncodingBits P.reviewFee + ratEncodingBits fee + 1)^degree

def VariableGammaPolynomialData : Prop :=
  ∃ C degree : ℕ, 0 < C ∧ ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ), 0 ≤ fee →
    P.numericalSize fee ≤ C * (P.certificate.stages + ratEncodingBits P.certificate.gamma +
      ratEncodingBits P.certificate.risk + ratEncodingBits P.reviewFee + ratEncodingBits fee +
        ⌈P.certificate.gamma⁻¹⌉₊ + 1)^degree

/-- Partial D27 data-bit coverage only. `Computation.ComputationalClaims`
also states the concrete rational/bit machines, costed evaluation, peak live
space and actual fair-bit sampler obligations. All remain pending proofs;
this conjunction alone is not the full D27 target. -/
def CachedDataBitClaims (P : PaperProofs.Paid.Parameters) : Prop :=
  P.MenuBitClaims ∧ CalibrationBitClaims ∧ MixtureBitClaims ∧ P.PositiveGapBitClaims ∧
    FixedGammaPolynomialData P.certificate.gamma ∧ VariableGammaPolynomialData

end PaperProofs.Paid.Parameters
