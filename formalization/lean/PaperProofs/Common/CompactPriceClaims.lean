module

public import PaperProofs.Common.SymbolicPrice
public import PaperProofs.Common.RationalControllerComputation
public import PaperProofs.Structure.CompactControllerClaims

/-!
Pending COMPLETE L01, frozen prices.tex:127--152.
Only the integer table callback replaces the generic rank/picker. In
particular the parser below accepts the TABLE's actual committed tool.
Different maximizing ties do not assert equal paths, bills or native runs.

All original rational tests, budget updates, actual handles, permissions,
fees, observation quotas and numeric H/H0 are retained. H0 is the source's
complete-execution bound for THIS selected table controller. No risk, price,
alignment, oracle correctness or finite-expectation premise is added.

Exact symbolic output is the existing fixed rational/add/mul/div/log AST.
Machine inputs contain no coefficient, KL value, head indices, table, rank,
tool answer or run trace. Internal callback words used by local arithmetic
must be outputs of actual charged A19 calls on the SAME persistent heap.
All claims below remain unproved, including the matching statistical upper.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native.CompactPrice

open PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree


variable {I : Instance} {bits : ℕ}

def tableReply (I : Instance) (available : Finset I.Tool) (stage : I.Stage)
    (used : Finset I.Tool) : IndexedQuery.Reply I.toolCount :=
  CompactControllerClaims.callback I.toolCount I.compatibility ⟨stage.val, by have := stage.isLt; omega⟩
    ((Finset.univ \ available) ∪ used)

def tableKind (I : Instance) (available : Finset I.Tool)
    (cache : ReferenceReplayCache I) : Option ReferenceBudgetCase := do
  let stage ← referenceReplayStage I cache
  let reply := tableReply I available stage (historyUsed cache.entryHistory)
  referenceCaseOfRanks reply.rank reply.bad

def tableTarget (I : Instance) (available : Finset I.Tool) (risk : ℚ)
    (cache : ReferenceReplayCache I) : Option ℚ := do
  if cache.halted || decide (cache.phase ≠ .testing) then none else do
  let kind ← tableKind I available cache
  let current ← referenceReplayRisk risk cache
  if 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount then
    referenceBudgetTarget kind current else none

/-- Same public grammar and original budget labels, accepting the table tie. -/
def tableStep (input : StatisticalInput I) (available : Finset I.Tool) (risk : ℚ)
    (cache : ReferenceReplayCache I) (event : VisibleEvent I) : Option (ReferenceReplayCache I) :=
  if cache.halted then none else
  let recorded := { cache with seen := cache.seen ++ [event] }
  match event with
  | .observation i symbol => do
    let stage ← referenceReplayStage I cache
    if i = stage ∧ symbol < (input.experiment i).alphabetSize ∧ cache.phase = .testing ∧
        (tableTarget I available risk cache).isSome then some recorded else none
  | .wrote i _ serial => do
    let stage ← referenceReplayStage I cache
    let _ ← tableKind I available cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ serial = (historyActions cache.seen).length ∧ cache.phase = .testing then
      some { recorded with phase := .written } else none
  | .report i truth serial => do
    let stage ← referenceReplayStage I cache
    let written ← historyWrite cache.seen stage
    let kind ← tableKind I available cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ serial = written.2 ∧ cache.phase = .written ∧ cache.events.length < I.stageCount then
      some { recorded with events := cache.events ++ [(kind, decide (written.1 ≠ truth))], phase := .reported }
    else none
  | .committed handle tool => do
    let stage ← referenceReplayStage I cache
    let _ ← referenceReplayRisk risk cache
    if cache.phase = .reported ∧ referenceReplayMismatch cache stage handle ∧
        tool ∈ I.eligible stage ∧ tool ∉ historyUsed cache.seen ∧ tool ∈ available ∧
        (tableReply I available stage (historyUsed cache.entryHistory)).tool = some tool then
      some { recorded with phase := .allocated tool } else none
  | .executed handle tool => do
    let stage ← referenceReplayStage I cache
    if cache.phase = .allocated tool ∧ referenceReplayMismatch cache stage handle then
      some { recorded with phase := .executed tool } else none
  | .advanced i => do
    let stage ← referenceReplayStage I cache
    let _ ← referenceReplayRisk risk cache
    if i = stage ∧ ((cache.phase = .reported ∧ referenceReplayCorrect cache stage) ∨
        ∃ tool, cache.phase = .executed tool) then
      some { recorded with entryHistory := recorded.seen, phase := .testing } else none
  | .stopped =>
    if historyCursor cache.seen = I.stageCount ∧ cache.phase = .testing then
      some { recorded with halted := true } else none
  | .abandoned =>
    if cache.phase ≠ .written then some { recorded with halted := true } else none

def tableReplay (input : StatisticalInput I) (available : Finset I.Tool) (risk : ℚ)
    (history : List (VisibleEvent I)) : Option (ReferenceReplayCache I) := do
  if 0 < risk ∧ risk ≤ 1 / 2 then pure () else none
  let cache ← history.foldlM (tableStep input available risk) (referenceReplayInitial I)
  if cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history then some cache else none

def tableTestingAction (input : StatisticalInput I) (available : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage) : Action I :=
  match tableKind I available cache with
  | none => .abandon
  | some .infiniteRank => .write stage false
  | some .noTool | some (.finiteBad _) =>
    match tableTarget I available risk cache with
    | none => .abandon
    | some target =>
      if hvalid : ∀ symbol ∈ historyObservations cache.seen stage,
          symbol < (input.experiment stage).alphabetSize then
        let word := historyObservationWord input cache.seen stage hvalid
        if (input.experiment stage).rationalWordHits target word then
          .write stage ((input.experiment stage).rationalWordMAP word)
        else match limit with
          | none => .review stage
          | some quota => if (historyObservations cache.seen stage).length < quota stage then .review stage else .abandon
      else .abandon

def tableCandidate (input : StatisticalInput I) (available : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I)) : Action I :=
  match tableReplay input available risk history with
  | none => .abandon
  | some cache =>
    if cache.halted then .stop else
    match referenceReplayStage I cache with
    | none => if historyCursor history = I.stageCount then .stop else .abandon
    | some stage =>
      match cache.phase with
      | .testing => tableTestingAction input available risk limit cache stage
      | .written => .abandon
      | .reported =>
        if referenceReplayCorrect cache stage then .advance stage else
        match referenceReplayRisk risk cache, referenceVisibleHandle history stage,
            (tableReply I available stage (historyUsed cache.entryHistory)).tool with
        | some _, some handle, some tool => .allocate handle tool
        | _, _, _ => .abandon
      | .allocated tool =>
        match referenceVisibleHandle history stage with
        | none => .abandon
        | some handle => .execute handle tool
      | .executed _ => .advance stage

def tableRule (input : StatisticalInput I) (available : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) : PolicyRule I Unit := fun _ history =>
  let action := tableCandidate input available risk limit history
  if historyAllowsAction history action then action else .abandon

/-- Same formula at the SAME public entry cache. This is deliberately NOT
an equality of generic/table parsers or runs with different tool ties. -/
def CallbackFormulaClaims : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
    ∀ (available : Finset I.Tool) (cache : ReferenceReplayCache I) (risk : ℚ),
      tableKind I available cache = referenceAvailableKind I available cache ∧
      tableTarget I available risk cache = referenceAvailableCacheTarget I available risk cache

def criticalIndices (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q)) : List ℕ :=
  let initial := CompactControllerClaims.callback q full ⟨0, by omega⟩ used
  if initial.rank = ⊤ then [] else
    ((List.finRange full.length).filter (fun stage =>
      decide ((CompactControllerClaims.callback q full ⟨stage.val, by have := stage.isLt; omega⟩ used).bad + 1 = initial.rank))).map Fin.val

def headWords (q : ℕ) (full : List (Finset (Fin q))) (used : Finset (Fin q)) : List ℕ :=
  [AlgorithmClaims.encodeRank q (CompactControllerClaims.callback q full ⟨0, by omega⟩ used).rank, (criticalIndices q full used).length] ++
    criticalIndices q full used

def headWork (q : ℕ) (full : List (Finset (Fin q))) : ℕ :=
  (full.length + 1) * CompactControllerClaims.liveWork q (CompactControllerClaims.treeSize q full)

def encodeExpr : PaperProofs.Common.SymbolicPrice.Expr → List RationalControllerComputation.Datum
  | .rational value => [.natural 0, .rational value]
  | .add left right => .natural 1 :: encodeExpr left ++ encodeExpr right
  | .multiply left right => .natural 2 :: encodeExpr left ++ encodeExpr right
  | .divide left right => .natural 3 :: encodeExpr left ++ encodeExpr right
  | .log argument => .natural 4 :: encodeExpr argument

def symbolicInput (input : StatisticalInput I) (available : Finset I.Tool) : List Bool :=
  RationalControllerComputation.encode (RationalControllerComputation.rawInstance input ++ RationalControllerComputation.rawSet available)

def symbolicOutput (input : StatisticalInput I) (available : Finset I.Tool) : List Bool :=
  RationalControllerComputation.encode ((headWords I.toolCount I.compatibility (Finset.univ \ available)).map RationalControllerComputation.Datum.natural ++
    encodeExpr (PaperProofs.Common.SymbolicPrice.inputExpression input available))

structure Implementation where
  preprocessor : List AlgorithmClaims.PackingOp
  live : List AlgorithmClaims.PackingOp
  heads : List AlgorithmClaims.PackingOp
  symbolicStates : ℕ
  symbolicMachine : RationalControllerComputation.Machine symbolicStates
  plannerStates : ℕ
  plannerMachine : RationalControllerComputation.Machine plannerStates
  scalar : RationalControllerComputation.Implementation

def HeadExtractionClaims (constant wordFactor scratchFactor : ℕ) (implementation : Implementation) : Prop :=
  ∀ (q : ℕ) (full : List (Finset (Fin q))), LaminarSchedule full → ∀ used : Finset (Fin q),
    let N := full.length
    let t := CompactControllerClaims.treeSize q full
    let bits := AlgorithmClaims.indexWidth wordFactor N q
    let capWords := CompactControllerClaims.capacityWords scratchFactor N q t
    let heapWords := CompactControllerClaims.physicalHeaderWords + AlgorithmClaims.packedCapacityWords q capWords bits + scratchFactor * (N + q + t + 1)
    let empty := fun _ => BitVec.ofNat bits 0
    let source := CompactControllerClaims.controllerInput q full used
    ∃ preSteps headSteps : ℕ,
    let built := AlgorithmClaims.packingRun source implementation.preprocessor preSteps (AlgorithmClaims.packingInitial empty)
    let result := AlgorithmClaims.packingRun (CompactControllerClaims.callInput q full .query) implementation.heads headSteps (AlgorithmClaims.packingInitial built.heap)
    RawTreePreprocessingClaims.DynamicRunCorrect heapWords source implementation.preprocessor preSteps empty ∧
    RawTreePreprocessingClaims.totalCost heapWords source implementation.preprocessor preSteps empty ≤ constant * CompactControllerClaims.preprocessingWork N q t ∧
    CompactControllerClaims.HeapRepresents q full capWords ⟨0, used, false⟩ built.heap ∧
    RawTreePreprocessingClaims.DynamicRunCorrect heapWords (CompactControllerClaims.callInput q full .query) implementation.heads headSteps built.heap ∧
    CompactControllerClaims.callCost q full implementation.heads .query headSteps built.heap ≤ constant * headWork q full ∧
    CompactControllerClaims.HeapRepresents q full capWords ⟨N, used, false⟩ result.heap ∧
    let base := (result.register .index).toNat
    base + (headWords q full used).length ≤ heapWords ∧
    RawTreePreprocessingClaims.heapWordsAt result.heap base (headWords q full used).length = headWords q full used

def SymbolicCompilationClaims (constant degree : ℕ) (implementation : Implementation) : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I) (available : Finset I.Tool),
    criticalIndices I.toolCount I.compatibility (Finset.univ \ available) = (PaperProofs.Common.SymbolicPrice.inputHeads input available).map Prod.fst ∧
    (PaperProofs.Common.SymbolicPrice.inputExpression input available).eval = input.orderedCoefficient available ∧
    RationalControllerComputation.computes implementation.symbolicMachine (symbolicInput input available) (symbolicOutput input available)
      (constant * ((symbolicInput input available).length +
        CompactControllerClaims.preprocessingWork I.stageCount I.toolCount (CompactControllerClaims.treeSize I.toolCount I.compatibility) + 1)^degree)
      (constant * ((symbolicInput input available).length +
        CompactControllerClaims.preprocessingWork I.stageCount I.toolCount (CompactControllerClaims.treeSize I.toolCount I.compatibility) + 1)^degree)

/-- Same ORIGINAL complete-H0 and numeric certificate, for THIS table tie. -/
structure OriginalQualification (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ) : Prop where
  stage_quota : ∀ stage, referenceQuota input exponent stage ≤ C.reviewQuota stage
  total_calls : C.normalCallBound + ∑ stage, referenceQuota input exponent stage +
    min I.stageCount I.toolCount ≤ C.totalCallCap
  normal_completed : CompletedNormalCallBound input C .uncapped accounting
    (tableRule input available budget (some (referenceQuota input exponent))) C.normalCallBound

def declaration (history : List (VisibleEvent I)) (stage : I.Stage) : CompactControllerClaims.Command :=
  match historyWrite history stage, historyReport history stage with
  | some (written, _), some (truth, _) => if written = truth then .correct else .error
  | _, _ => .correct

/-- Commands arise from actual public reports/advances. The current query
is already present before any local testing. A fatal unadvanced stage does
not consume a fake correction. -/
def commandsAt (I : Instance) (history : List (VisibleEvent I)) : List CompactControllerClaims.Command :=
  ((List.finRange (min (historyCursor history) I.stageCount)).flatMap (fun stage =>
    let current : I.Stage := ⟨stage.val, lt_of_lt_of_le stage.isLt (min_le_right _ _)⟩
    [.query, declaration history current])) ++
      if historyCursor history < I.stageCount then [.query] else []

/-- Internal words are read from ACTUAL physical callback output registers. -/
def queryRecords (q : ℕ) (full : List (Finset (Fin q))) (program : List AlgorithmClaims.PackingOp) :
    List CompactControllerClaims.Command → List ℕ → (BitVec bits → BitVec bits) → List ℕ
  | [], _, _ => []
  | _, [], _ => []
  | command :: later, steps :: counts, heap =>
    let result := AlgorithmClaims.packingRun (CompactControllerClaims.callInput q full command) program steps (AlgorithmClaims.packingInitial heap)
    (if command = .query then
      [(result.register .value).toNat, (result.register .old).toNat,
        (result.register .fresh).toNat, (result.register .index).toNat] else []) ++
      queryRecords q full program later counts result.heap

def plannerInput (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (records : List ℕ) : List Bool :=
  RationalControllerComputation.encode
    ([.natural I.stageCount, .natural I.toolCount] ++
      (List.finRange I.stageCount).flatMap (fun stage =>
        RationalControllerComputation.rawExperiment (input.experiment stage)) ++
      RationalControllerComputation.rawContract C ++ [.rational budget] ++
      RationalControllerComputation.rawSet available ++ RationalControllerComputation.encodeHistory history) ++
    RationalControllerComputation.encode (records.map RationalControllerComputation.Datum.natural)

/-- Genuine charged hybrid execution: a persistent physical table engine
and ordinary local Boolean computation. The callback records are produced
inside this very execution, never supplied as an external rank oracle. -/
def ActualCompactCost (constant wordFactor scratchFactor degree : ℕ) (implementation : Implementation)
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ)
    (policy : Policy input C .native accounting Unit) : Prop :=
  let N := I.stageCount
  let q := I.toolCount
  let t := CompactControllerClaims.treeSize q I.compatibility
  let bits := AlgorithmClaims.indexWidth wordFactor N q
  let capWords := CompactControllerClaims.capacityWords scratchFactor N q t
  let heapWords := CompactControllerClaims.physicalHeaderWords + AlgorithmClaims.packedCapacityWords q capWords bits + scratchFactor * (N + q + t + 1)
  let empty := fun _ => BitVec.ofNat bits 0
  let source := CompactControllerClaims.controllerInput q I.compatibility (Finset.univ \ available)
  let horizon := quotaActionBound I (referenceQuota input exponent) + 1
  let allowance := constant * (RationalControllerComputation.arithmeticScale input C budget + CompactControllerClaims.preprocessingWork N q t + 1)^degree
  ∃ preSteps : ℕ,
  let built := AlgorithmClaims.packingRun source implementation.preprocessor preSteps (AlgorithmClaims.packingInitial empty)
  RawTreePreprocessingClaims.DynamicRunCorrect heapWords source implementation.preprocessor preSteps empty ∧
  RawTreePreprocessingClaims.totalCost heapWords source implementation.preprocessor preSteps empty ≤ constant * CompactControllerClaims.preprocessingWork N q t ∧
  CompactControllerClaims.HeapRepresents q I.compatibility capWords ⟨0, Finset.univ \ available, false⟩ built.heap ∧
  ∀ sample : Unit × input.World,
  let final := run input C .native accounting policy.rule sample horizon
  final.halted = true ∧
  ∃ counts : List ℕ,
  let commands := commandsAt I final.history
  counts.length = commands.length ∧ commands.length ≤ 2 * N + 1 ∧
  CompactControllerClaims.CommandsRunClaims constant q I.compatibility capWords heapWords implementation.live
    ⟨0, Finset.univ \ available, false⟩ commands counts built.heap ∧
  CompactControllerClaims.commandsCost q I.compatibility implementation.live commands counts built.heap ≤ constant * (N + 1) * CompactControllerClaims.liveWork q t ∧
  ∃ preparationTrace preparationFinal,
  RationalControllerComputation.Runs implementation.scalar.preparationMachine (RationalControllerComputation.preparationInput input C budget) preparationTrace preparationFinal ∧
  preparationFinal.Tape.right₀ = Turing.ListBlank.mk (RationalControllerComputation.preparationOutput input C budget) ∧
  RationalControllerComputation.visitedSpace implementation.scalar.preparationMachine
    (RationalControllerComputation.preparationInput input C budget).length preparationTrace ≤ allowance ∧
  ∃ traces : Fin horizon → List (RationalControllerComputation.MachineState implementation.plannerStates),
  (∀ clock : Fin horizon,
    let state := run input C .native accounting policy.rule sample clock.val
    let current := commandsAt I state.history
    current.IsPrefix commands ∧
    CompactControllerClaims.CommandsRunClaims constant q I.compatibility capWords heapWords implementation.live
      ⟨0, Finset.univ \ available, false⟩ current (counts.take current.length) built.heap ∧
    if state.halted then traces clock = [] else
      let records := queryRecords q I.compatibility implementation.live current (counts.take current.length) built.heap
      ∃ bitFinal, RationalControllerComputation.Runs implementation.plannerMachine (plannerInput input C available budget state.history records)
        (traces clock) bitFinal ∧
        bitFinal.Tape.right₀ = Turing.ListBlank.mk (RationalControllerComputation.encode (RationalControllerComputation.encodeAction (policy.rule () state.history))) ∧
        RationalControllerComputation.visitedSpace implementation.plannerMachine
          (plannerInput input C available budget state.history records).length (traces clock) ≤ allowance) ∧
  preparationTrace.length + ∑ clock, (traces clock).length ≤ allowance

def NativeControllerClaims (constant wordFactor scratchFactor degree : ℕ) (implementation : Implementation) : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
  ∀ (input : StatisticalInput I) (C : Contract I) (_hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ),
    0 < delta → delta ≤ 1 / 2 → ∀ (budget : ℚ) (exponent : ℕ),
    ReferenceRiskChoice I.stageCount delta exponent budget →
    OriginalQualification input C accounting available budget exponent →
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = tableRule input available budget (some (referenceQuota input exponent)) ∧
      (∀ sample clock, run input C .native accounting policy.rule sample clock =
        run input C .uncapped accounting (tableRule input available budget (some (referenceQuota input exponent))) sample clock) ∧
      (∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C ∧
        (run input C .native accounting policy.rule sample clock).ledger.normalCalls ≤ (C.normalCallBound : ℕ∞)) ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting (tableRule input available budget none) (Measure.dirac ()) ∧
      ActualCompactCost constant wordFactor scratchFactor degree implementation input C accounting
        available budget exponent policy

/-- Fixed ORIGINAL input precedes cutoff; no leading-price/risk performance
claim is an input. In particular this upper is proved for the table tie,
not transported from the generic run by an unjustified equality. -/
def SharpUpperClaims : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I)
    (available : Finset I.Tool) (depth : ℕ), errorRank I.compatibility available = (depth : ℕ∞) →
    ∀ epsilon : ℝ, 0 < epsilon → ∃ cutoff : ℝ, 0 < cutoff ∧
    ∀ (delta : ℝ), 0 < delta → delta < cutoff → delta ≤ 1 / 2 →
    ∀ (budget : ℚ) (exponent : ℕ), ReferenceRiskChoice I.stageCount delta exponent budget →
    ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I),
    OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        policy.rule = tableRule input available budget (some (referenceQuota input exponent)) ∧
        risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
          ENNReal.ofReal ((1 + epsilon) * (PaperProofs.Common.SymbolicPrice.inputExpression input available).eval * iteratedLog depth delta⁻¹)

def InfiniteRankClaims : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility → ∀ (input : StatisticalInput I)
    (available : Finset I.Tool), errorRank I.compatibility available = ⊤ →
    ∀ (C : Contract I) (_hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
      (budget : ℚ) (exponent : ℕ), 0 < budget → budget ≤ 1 / 2 →
    OriginalQualification input C accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        policy.rule = tableRule input available budget (some (referenceQuota input exponent)) ∧
        risk input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedObservationBill input C .native accounting policy.rule (Measure.dirac ()) = 0 ∧
        expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
          (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection

/-- Complete L01 target. Every pending dependency is a CONCLUSION here.
No table/structural/statistical oracle is supplied as a new premise. -/
def FullClaims : Prop :=
  CompactControllerClaims.FullClaims.{0} ∧ CallbackFormulaClaims ∧ SharpUpperClaims ∧ InfiniteRankClaims ∧
    ∃ (constant wordFactor scratchFactor degree : ℕ) (implementation : Implementation),
      0 < constant ∧ 0 < wordFactor ∧ 0 < scratchFactor ∧ 0 < degree ∧
      HeadExtractionClaims constant wordFactor scratchFactor implementation ∧
      SymbolicCompilationClaims constant degree implementation ∧
      RationalControllerComputation.localArithmeticClaims constant degree implementation.scalar ∧
      NativeControllerClaims constant wordFactor scratchFactor degree implementation

end PaperProofs.Common.Native.CompactPrice
