module

public import PaperProofs.Common.GeneralNormalFeeReference
public import PaperProofs.Common.NativeObservedWords
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
Pending full B23 computational target for frozen price-proofs.tex:294--300.
The machine is an ordinary finite-control Bool TM0: rational multiplication,
division, integer log/ceil, graph ranks and history replay are NOT primitives.
All finite machines and complexity constants precede all original inputs.

Only original rational probabilities/fees, explicit incidence, the original
contract numbers, a selected rational reference risk and FINITE public words
are encoded.  No KL/log oracle, target, quota, rank, table, action or run trace
is supplied.  Original real delta enters only the proved ReferenceRiskChoice
interface; its executable rational budget computes the SAME original exponent.

For a general graph the existing generic rank evaluator may be exponential.
The statistical arithmetic bounds are polynomial in input bit lengths and
numerical quotas; the entire rule's bound ALSO displays its structural factor.
Replacing that factor by the laminar A17 implementation is the separate A19
integration. No polynomial-in-log(H) or native-wall-clock claim is asserted.
Everything named Claims below is an unproved Prop, not a machine/Policy field.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native.RationalControllerComputation

open PaperProofs.Statistics

variable {I : Instance}

inductive Datum where
  | natural (value : ℕ)
  | rational (value : ℚ)
  deriving DecidableEq

def natBits (value : ℕ) : ℕ := Nat.log2 value + 1

/-- Standard finite sign/magnitude binary encoding, with a length prefix
linear in bit length. Zero receives one bit. No unary numeric input. -/
def encodeNat (value : ℕ) : List Bool :=
  List.replicate (natBits value) true ++ [false] ++
    List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)

def encodeDatum : Datum → List Bool
  | .natural value => false :: encodeNat value
  | .rational value => [true, decide (value < 0)] ++ encodeNat value.num.natAbs ++ encodeNat value.den

/-- The final true delimiter distinguishes finite outputs from blank tails. -/
def encode (data : List Datum) : List Bool :=
  encodeNat data.length ++ data.flatMap encodeDatum ++ [true]

def boolDatum (value : Bool) : Datum := .natural (if value then 1 else 0)

def rawExperiment (E : BinaryExperiment) : List Datum :=
  [.natural E.alphabetSize, .rational E.priorOne, .rational E.observationFee] ++
    [false, true].flatMap (fun truth => (List.finRange E.alphabetSize).map
      (fun symbol => Datum.rational (E.channel truth symbol)))

def rawSet {q : ℕ} (tools : Finset (Fin q)) : List Datum :=
  (List.finRange q).map (fun tool => boolDatum (decide (tool ∈ tools)))

/-- Original instance/experiment/fee data only, with explicit incidence.
Proof fields are omitted. No computed statistic or structural answer occurs. -/
def rawInstance (input : StatisticalInput I) : List Datum :=
  [.natural I.stageCount, .natural I.toolCount] ++ I.compatibility.flatMap rawSet ++
    (List.finRange I.stageCount).flatMap (fun stage => rawExperiment (input.experiment stage)) ++
    (List.finRange I.stageCount).flatMap (fun stage => (List.finRange I.toolCount).map
      (fun tool => Datum.rational (input.correctionFee stage tool)))

def rawContract (C : Contract I) : List Datum :=
  [boolDatum (decide (C.reporting = .early)), boolDatum (decide (C.allocation = .currentWindow)),
    boolDatum (decide (C.execution = .currentWindow)), .natural C.totalCallCap, .natural C.normalCallBound] ++
      (List.finRange I.stageCount).map (fun stage => Datum.natural (C.reviewQuota stage))

def encodeHandle (handle : MismatchHandle I) : List Datum :=
  [.natural handle.stage.val, .natural handle.writeSerial]

def encodeAction : Action I → List Datum
  | .review stage => [.natural 0, .natural stage.val]
  | .write stage value => [.natural 1, .natural stage.val, boolDatum value]
  | .allocate handle tool => .natural 2 :: encodeHandle handle ++ [.natural tool.val]
  | .execute handle tool => .natural 3 :: encodeHandle handle ++ [.natural tool.val]
  | .advance stage => [.natural 4, .natural stage.val]
  | .stop => [.natural 5]
  | .abandon => [.natural 6]

def encodeEvent : VisibleEvent I → List Datum
  | .observation stage symbol => [.natural 0, .natural stage.val, .natural symbol]
  | .wrote stage value serial => [.natural 1, .natural stage.val, boolDatum value, .natural serial]
  | .report stage truth serial => [.natural 2, .natural stage.val, boolDatum truth, .natural serial]
  | .committed handle tool => .natural 3 :: encodeHandle handle ++ [.natural tool.val]
  | .executed handle tool => .natural 4 :: encodeHandle handle ++ [.natural tool.val]
  | .advanced stage => [.natural 5, .natural stage.val]
  | .stopped => [.natural 6]
  | .abandoned => [.natural 7]

def encodeHistory (history : List (VisibleEvent I)) : List Datum :=
  .natural history.length :: history.flatMap encodeEvent

def rawWord (E : BinaryExperiment) (word : E.StoppedWord) : List Datum :=
  .natural word.1 :: (List.finRange word.1).map (fun position => .natural (word.2 position).val)

def wordInput (E : BinaryExperiment) (target : ℚ) (word : E.StoppedWord) : List Bool :=
  encode (rawExperiment E ++ [.rational target] ++ rawWord E word)

def wordOutput (E : BinaryExperiment) (target : ℚ) (word : E.StoppedWord) : List Bool :=
  encode [.rational (E.rationalWordOdds word), boolDatum (E.rationalWordHits target word),
    boolDatum (E.rationalWordMAP word)]

def thresholdOutput (risk : ℚ) (depth : ℕ) : List Bool :=
  let target := controllerTarget risk depth
  encode [.natural (controllerB risk depth), .rational target,
    .rational (controllerBadRisk risk target), .rational ((1 - target) / target),
    .rational (target / (1 - target))]

def computedExponent (budget : ℚ) : ℕ := BinaryExperiment.quotaExponent budget I.stageCount

def computedQuotas (input : StatisticalInput I) (budget : ℚ) : I.Stage → ℕ :=
  referenceQuota input (computedExponent (I := I) budget)

def preparationInput (input : StatisticalInput I) (C : Contract I) (budget : ℚ) : List Bool :=
  encode (rawInstance input ++ rawContract C ++ [.rational budget])

/-- Checks only the ORIGINAL numeric resource conditions. A normal-I/O H0
certificate is not computable from these numbers and is NOT faked here. -/
def numericQualification (input : StatisticalInput I) (C : Contract I) (budget : ℚ) : Bool :=
  decide ((∀ stage, computedQuotas input budget stage ≤ C.reviewQuota stage) ∧
    C.normalCallBound + ∑ stage, computedQuotas input budget stage +
      min I.stageCount I.toolCount ≤ C.totalCallCap)

def preparationOutput (input : StatisticalInput I) (C : Contract I) (budget : ℚ) : List Bool :=
  encode ([.natural (computedExponent (I := I) budget), boolDatum (numericQualification input C budget)] ++
    (List.finRange I.stageCount).flatMap (fun stage =>
      let E := input.experiment stage
      [.rational E.channelDriftLower, .natural E.channelIntegerMax, .natural E.priorIntegerMax,
        .natural (computedQuotas input budget stage)]))

def controllerInput (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : List Bool :=
  encode (rawInstance input ++ rawContract C ++ [.rational budget] ++ rawSet available ++ encodeHistory history)

def computedRule (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) : PolicyRule I Unit :=
  referenceRule input available budget (some (computedQuotas input budget))

def controllerOutput (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (history : List (VisibleEvent I)) : List Bool :=
  encode (encodeAction (computedRule input available budget () history))

/-- Representation correctness is also pending: equality of returned bits
must identify the actual native action, not merely an ambiguous label. -/
def EncodingClaims : Prop :=
  Function.Injective encode ∧
    (∀ I : Instance, Function.Injective (encodeAction (I := I))) ∧
    ∀ I : Instance, Function.Injective (encodeHistory (I := I))

abbrev Machine (states : ℕ) := Turing.TM0.Machine Bool (Fin (states + 1))
abbrev MachineState (states : ℕ) := Turing.TM0.Cfg Bool (Fin (states + 1))

/-- Actual finite-control bit transitions, including a true final halt.
Invalid or merely labelled host computations are not accepted runs. -/
def Runs {states : ℕ} (machine : Machine states) (input : List Bool)
    (trace : List (MachineState states)) (final : MachineState states) : Prop :=
  trace.head? = some (Turing.TM0.init input) ∧
    trace.IsChain (fun before after => Turing.TM0.step machine before = some after) ∧
    trace.getLast? = some final ∧ Turing.TM0.step machine final = none ∧
    final ∈ StateTransition.eval (Turing.TM0.step machine) (Turing.TM0.init input)

def displacement {states : ℕ} (machine : Machine states) (state : MachineState states) : ℤ :=
  match machine state.q state.Tape.head with
  | some (_, .move .left) => -1
  | some (_, .move .right) => 1
  | _ => 0

def visitedSpace {states : ℕ} (machine : Machine states) (inputLength : ℕ)
    (trace : List (MachineState states)) : ℕ :=
  let positions := (trace.map (displacement machine)).scanl (· + ·) 0
  let high := positions.foldl max (inputLength : ℤ)
  let low := positions.foldl min 0
  (high - low).toNat + 1

def computes {states : ℕ} (machine : Machine states) (input output : List Bool)
    (time space : ℕ) : Prop :=
  ∃ trace final, Runs machine input trace final ∧
    final.Tape.right₀ = Turing.ListBlank.mk output ∧
    trace.length ≤ time ∧ visitedSpace machine input.length trace ≤ space

/-- All machines are finite code only; no correctness, cost or rank oracle
is provided as a field of this implementation. -/
structure Implementation where
  wordStates : ℕ
  wordMachine : Machine wordStates
  thresholdStates : ℕ
  thresholdMachine : Machine thresholdStates
  preparationStates : ℕ
  preparationMachine : Machine preparationStates
  controllerStates : ℕ
  controllerMachine : Machine controllerStates

def numericalQuota (input : StatisticalInput I) (budget : ℚ) : ℕ :=
  ∑ stage, computedQuotas input budget stage

def inputSize (input : StatisticalInput I) (C : Contract I) (budget : ℚ) : ℕ :=
  (preparationInput input C budget).length + I.stageCount + I.toolCount + 1

/-- An explicit allowance for the existing general-graph rank recursion.
It is independent of risk, channel probabilities, fees and native quotas.
This factor is NOT called polynomial structural preprocessing. -/
def generalStructureFactor (I : Instance) : ℕ :=
  (I.stageCount + 1) * (I.toolCount + 2) ^ (I.stageCount + 1)

def arithmeticScale (input : StatisticalInput I) (C : Contract I) (budget : ℚ) : ℕ :=
  inputSize input C budget + numericalQuota input budget + 1

def localArithmeticClaims (constant degree : ℕ) (implementation : Implementation) : Prop :=
  (∀ (E : BinaryExperiment) (target : ℚ), 0 < target → target ≤ 1 / 4 →
    ∀ word : E.StoppedWord,
    computes implementation.wordMachine (wordInput E target word) (wordOutput E target word)
      (constant * ((wordInput E target word).length + word.1 + 1)^degree)
      (constant * ((wordInput E target word).length + word.1 + 1)^degree)) ∧
  (∀ (risk : ℚ), 0 < risk → risk ≤ 1 / 4 → ∀ depth : ℕ, 1 ≤ depth →
    let input := encode [.rational risk, .natural depth]
    computes implementation.thresholdMachine input (thresholdOutput risk depth)
      (constant * (input.length + depth + 1)^degree)
      (constant * (input.length + depth + 1)^degree)) ∧
  (∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (budget : ℚ),
    0 < budget → budget ≤ 1 / 2 →
    computes implementation.preparationMachine (preparationInput input C budget)
      (preparationOutput input C budget)
      (constant * (arithmeticScale input C budget)^degree)
      (constant * (arithmeticScale input C budget)^degree))

/-- One genuine bit-machine call returns exactly the original visible
reference rule, including malformed-history guards, inclusive T=Q, T=0,
actual handles and the original generic maximizing tool. It computes the
structural values from incidence, not a supplied rank/answer oracle. -/
def visibleRuleClaims (constant degree : ℕ) (implementation : Implementation) : Prop :=
  ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I)
    (available : Finset I.Tool) (budget : ℚ), 0 < budget → budget ≤ 1 / 2 →
    ∀ history : List (VisibleEvent I),
    let bits := (controllerInput input C available budget history).length
    let allowance := constant * generalStructureFactor I *
      (arithmeticScale input C budget + bits + 1)^degree
    computes implementation.controllerMachine (controllerInput input C available budget history)
      (controllerOutput input available budget history) allowance allowance

/-- Actual machine-call traces on a REAL native run. Only active clocks
invoke the local planner. The native observation/report responses are input
events; no hidden tape is passed to any local machine. Failed/abandoned
paths are included. This is not a count of solver labels. -/
def ActualExecutionCost (constant degree : ℕ) (implementation : Implementation)
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ)
    (policy : Policy input C .native accounting Unit) : Prop :=
  let horizon := quotaActionBound I (referenceQuota input exponent) + 1
  ∀ sample : Unit × input.World,
    (run input C .native accounting policy.rule sample horizon).halted = true ∧
    ∃ preparationTrace preparationFinal,
    Runs implementation.preparationMachine (preparationInput input C budget) preparationTrace preparationFinal ∧
    preparationFinal.Tape.right₀ = Turing.ListBlank.mk (preparationOutput input C budget) ∧
    visitedSpace implementation.preparationMachine (preparationInput input C budget).length preparationTrace ≤
      constant * (arithmeticScale input C budget)^degree ∧
    ∃ traces : Fin horizon → List (MachineState implementation.controllerStates),
    (∀ clock : Fin horizon,
      let state := run input C .native accounting policy.rule sample clock.val
      if state.halted then traces clock = [] else
        ∃ final, Runs implementation.controllerMachine
          (controllerInput input C available budget state.history) (traces clock) final ∧
          final.Tape.right₀ = Turing.ListBlank.mk (encode (encodeAction (policy.rule () state.history))) ∧
          visitedSpace implementation.controllerMachine
            (controllerInput input C available budget state.history).length (traces clock) ≤
              constant * generalStructureFactor I * (arithmeticScale input C budget)^degree) ∧
    preparationTrace.length +
      ∑ clock, (traces clock).length ≤
        constant * generalStructureFactor I * (arithmeticScale input C budget)^degree

/-- Original risk/exponent/H0/numeric qualification, not new implementability
or performance hypotheses. The actual selected native controller is explicit;
its local bit calls must return precisely its real actions and satisfy a
whole-path numerical-quota bit bound. No risk/cost/termination assumption is
inserted in this target. -/
def nativeControllerClaims (constant degree : ℕ) (implementation : Implementation) : Prop :=
  ∀ (I : Instance) (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (delta : ℝ), 0 < delta → delta ≤ 1 / 2 →
    ∀ (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ),
    ReferenceRiskChoice I.stageCount delta exponent budget →
    ∀ qualification : ReferenceCompleteOriginalQualification input C hcurrent.1 accounting available budget exponent,
      computedExponent (I := I) budget = exponent ∧ numericQualification input C budget = true ∧
      let policy := GeneralNormalFees.completeNativeReferencePolicy input C hcurrent.1 accounting
        available budget exponent qualification
      policy.rule = (referenceBoundedPolicy input C hcurrent.1 accounting available budget exponent).rule ∧
      (∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C) ∧
      ActualExecutionCost constant degree implementation input C accounting available budget exponent policy

/-- Full first-round B23 target. Exact Boolean-TM computations, local
polynomial statistical arithmetic, explicit general structural work, and
actual original-cap controller execution are all conclusions still to prove.
No Paid module is imported and no A17 complexity result is assumed here. -/
def RationalControllerComputationClaims : Prop :=
  ∃ (constant degree : ℕ) (implementation : Implementation), 0 < constant ∧ 0 < degree ∧
    EncodingClaims ∧ localArithmeticClaims constant degree implementation ∧
    visibleRuleClaims constant degree implementation ∧
    nativeControllerClaims constant degree implementation

end PaperProofs.Common.Native.RationalControllerComputation
