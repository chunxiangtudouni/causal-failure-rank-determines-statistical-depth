module

public import PaperProofs.Paid.CachedFrontend
public import PaperProofs.Structure.IndexedRAM
public import Mathlib.Computability.StateTransition
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
First-round computational obligations for frozen paid-proofs.tex:614--642.

The rational RAM below follows the project's existing indexed RAM convention:
finite registers, an indexed readonly input/program and explicit heap accesses.
Exact rational arithmetic has UNIT COST only in that model. A separate Mathlib
TM0 Boolean-tape refinement measures bit transitions and visited tape space.
No whole table, argmin, walk, search, log, power or sampling oracle is primitive.

All implementation programs are quantified BEFORE every paper input. Their
readonly input contains the original numeric parameters, never a desired output
table or an execution trace. Output is checked against the fixed CachedFrontend.
All implementation/time/space/bit/coin claims are pending Props, not machine
fields, not consequences of prior loop-label counts, and not new paper premises.

Exact rational coins use ordinary private fair bits and rejection. The source
claims no fixed worst-case fair-bit count or sampling-time bound; neither is
inserted below. Sampler nonreturn is explicit and must be proved null.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace PaperProofs.Paid.Computation

open Common
open PaperProofs.Paid.Parameters

abbrev Register := Structure.LaminarTree.IndexedRAM.Register

def registers : List Register := [.address, .index, .value, .total, .old, .fresh, .flag]

inductive Cell where
  | natural (value : ℕ)
  | rational (value : ℚ)
  deriving DecidableEq, Repr

def Cell.nat? : Cell → Option ℕ
  | .natural value => some value
  | _ => none

def Cell.rat? : Cell → Option ℚ
  | .rational value => some value
  | _ => none

def Cell.bits : Cell → ℕ
  | .natural value => 1 + natBits value
  | .rational value => 1 + ratEncodingBits value

inductive NatOp where
  | add | subtract | multiply | divide | modulo
  deriving DecidableEq

def NatOp.eval : NatOp → ℕ → ℕ → Option ℕ
  | .add, a, b => some (a + b)
  | .subtract, a, b => some (a - b)
  | .multiply, a, b => some (a * b)
  | .divide, a, b => if b = 0 then none else some (a / b)
  | .modulo, a, b => if b = 0 then none else some (a % b)

inductive RatOp where
  | add | subtract | multiply | divide
  deriving DecidableEq

def RatOp.eval : RatOp → ℚ → ℚ → Option ℚ
  | .add, a, b => some (a + b)
  | .subtract, a, b => some (a - b)
  | .multiply, a, b => some (a * b)
  | .divide, a, b => if b = 0 then none else some (a / b)

inductive Comparison where
  | equal | less | lessEqual
  deriving DecidableEq

def Comparison.nat (comparison : Comparison) (a b : ℕ) : Bool := match comparison with
  | .equal => a == b
  | .less => decide (a < b)
  | .lessEqual => decide (a ≤ b)

def Comparison.rat (comparison : Comparison) (a b : ℚ) : Bool := match comparison with
  | .equal => a == b
  | .less => decide (a < b)
  | .lessEqual => decide (a ≤ b)

/-- A rational word-RAM instruction has a fixed padded encoding. A rational
constant occupies one rational word in this unit-cost model, not one bit. -/
inductive Instruction where
  | constant (target : Register) (value : Cell)
  | move (target source : Register)
  | loadInput (target pointer : Register)
  | load (target pointer : Register)
  | store (pointer source : Register)
  | release (pointer : Register)
  | natOp (operation : NatOp) (target left right : Register)
  | ratOp (operation : RatOp) (target left right : Register)
  | natCompare (comparison : Comparison) (target left right : Register)
  | ratCompare (comparison : Comparison) (target left right : Register)
  | natToRat (target source : Register)
  | numeratorAbs (target source : Register)
  | denominator (target source : Register)
  | negative (target source : Register)
  | branchZero (condition : Register) (whenZero whenNonzero : ℕ)
  | jump (target : ℕ)
  | jumpIndirect (source : Register)
  | output (source : Register)
  | halt

abbrev Program := Array Instruction

structure State where
  register : Register → Cell
  heap : ℕ → Cell
  live : Finset ℕ
  pc : ℕ
  output : List Cell

def initial : State := ⟨fun _ => .natural 0, fun _ => .natural 0, ∅, 0, []⟩

def State.set (state : State) (target : Register) (value : Cell) : State :=
  { state with register := Function.update state.register target value }

def Instruction.execute (input : List Cell) (instruction : Instruction) (state : State) : Option State := do
  let after := { state with pc := state.pc + 1 }
  match instruction with
  | .constant target value => pure (after.set target value)
  | .move target source => pure (after.set target (state.register source))
  | .loadInput target pointer =>
    let address ← (state.register pointer).nat?
    let value ← input[address]?
    pure (after.set target value)
  | .load target pointer =>
    let address ← (state.register pointer).nat?
    if address ∈ state.live then pure (after.set target (state.heap address)) else none
  | .store pointer source =>
    let address ← (state.register pointer).nat?
    pure { after with heap := Function.update state.heap address (state.register source), live := insert address state.live }
  | .release pointer =>
    let address ← (state.register pointer).nat?
    pure { after with heap := Function.update state.heap address (.natural 0), live := state.live.erase address }
  | .natOp operation target left right =>
    let a ← (state.register left).nat?
    let b ← (state.register right).nat?
    let value ← operation.eval a b
    pure (after.set target (.natural value))
  | .ratOp operation target left right =>
    let a ← (state.register left).rat?
    let b ← (state.register right).rat?
    let value ← operation.eval a b
    pure (after.set target (.rational value))
  | .natCompare comparison target left right =>
    let a ← (state.register left).nat?
    let b ← (state.register right).nat?
    pure (after.set target (.natural (if comparison.nat a b then 1 else 0)))
  | .ratCompare comparison target left right =>
    let a ← (state.register left).rat?
    let b ← (state.register right).rat?
    pure (after.set target (.natural (if comparison.rat a b then 1 else 0)))
  | .natToRat target source =>
    let value ← (state.register source).nat?
    pure (after.set target (.rational value))
  | .numeratorAbs target source =>
    let value ← (state.register source).rat?
    pure (after.set target (.natural value.num.natAbs))
  | .denominator target source =>
    let value ← (state.register source).rat?
    pure (after.set target (.natural value.den))
  | .negative target source =>
    let value ← (state.register source).rat?
    pure (after.set target (.natural (if value < 0 then 1 else 0)))
  | .branchZero condition whenZero whenNonzero =>
    let value ← (state.register condition).nat?
    pure { after with pc := if value = 0 then whenZero else whenNonzero }
  | .jump target => pure { after with pc := target }
  | .jumpIndirect source =>
    let target ← (state.register source).nat?
    pure { after with pc := target }
  | .output source => pure { after with output := state.output ++ [state.register source] }
  | .halt => none

def step (program : Program) (input : List Cell) (state : State) : Option State := do
  let instruction ← program[state.pc]?
  instruction.execute input state

def eval (program : Program) (input : List Cell) : Part State :=
  StateTransition.eval (step program input) initial

inductive Primitive where
  | instructionWordRead | decode | pcArithmetic
  | registerRead | registerWrite | addressArithmetic
  | inputRead | heapRead | heapWrite | heapRelease | outputWrite
  | naturalArithmetic | rationalArithmetic | comparison | branch
  deriving DecidableEq

def Instruction.operations : Instruction → List Primitive
  | .constant _ _ => [.registerWrite]
  | .move _ _ => [.registerRead, .registerWrite]
  | .loadInput _ _ => [.registerRead, .addressArithmetic, .inputRead, .registerWrite]
  | .load _ _ => [.registerRead, .addressArithmetic, .heapRead, .registerWrite]
  | .store _ _ => [.registerRead, .registerRead, .addressArithmetic, .heapWrite]
  | .release _ => [.registerRead, .addressArithmetic, .heapRelease]
  | .natOp _ _ _ _ => [.registerRead, .registerRead, .naturalArithmetic, .registerWrite]
  | .ratOp _ _ _ _ => [.registerRead, .registerRead, .rationalArithmetic, .registerWrite]
  | .natCompare _ _ _ _ | .ratCompare _ _ _ _ => [.registerRead, .registerRead, .comparison, .registerWrite]
  | .natToRat _ _ | .numeratorAbs _ _ | .denominator _ _ | .negative _ _ =>
      [.registerRead, .naturalArithmetic, .registerWrite]
  | .branchZero _ _ _ => [.registerRead, .branch]
  | .jump _ => [.branch]
  | .jumpIndirect _ => [.registerRead, .branch]
  | .output _ => [.registerRead, .outputWrite]
  | .halt => []

def Instruction.primitives (instruction : Instruction) : List Primitive :=
  List.replicate 5 .instructionWordRead ++ List.replicate 4 .addressArithmetic ++
    [.decode, .pcArithmetic] ++ instruction.operations

def primitiveTrace (program : Program) (trace : List State) : List Primitive :=
  trace.flatMap fun state => ((program[state.pc]?).map Instruction.primitives).getD []

/-- The trace consists of actual successive machine states, including the
final fetched halt. Invalid fetch/type/division termination is not success. -/
def Runs (program : Program) (input : List Cell) (trace : List State) (final : State) : Prop :=
  trace.head? = some initial ∧
    trace.IsChain (fun before after => step program input before = some after) ∧
    trace.getLast? = some final ∧ program[final.pc]? = some .halt ∧ final ∈ eval program input

/-! Physical readonly code words and a word-addressed program counter.
The refinement below is a PENDING obligation. Thus the typed trace is not
silently taken as proof that an encoded program has the claimed cost. -/

def NatOp.word : NatOp → ℕ
  | .add => 0 | .subtract => 1 | .multiply => 2 | .divide => 3 | .modulo => 4

def NatOp.fromWord : ℕ → Option NatOp
  | 0 => some .add | 1 => some .subtract | 2 => some .multiply | 3 => some .divide | 4 => some .modulo
  | _ => none

def RatOp.word : RatOp → ℕ
  | .add => 0 | .subtract => 1 | .multiply => 2 | .divide => 3

def RatOp.fromWord : ℕ → Option RatOp
  | 0 => some .add | 1 => some .subtract | 2 => some .multiply | 3 => some .divide
  | _ => none

def Comparison.word : Comparison → ℕ
  | .equal => 0 | .less => 1 | .lessEqual => 2

def Comparison.fromWord : ℕ → Option Comparison
  | 0 => some .equal | 1 => some .less | 2 => some .lessEqual
  | _ => none

def registerWord (register : Register) : Cell := .natural register.word

def registerFromWord (word : Cell) : Option Register := do
  let value ← word.nat?
  Structure.LaminarTree.IndexedRAM.Register.fromWord value

/-- Padded five-word encoding; one arbitrary rational word is permitted only
in the separate rational unit-cost model. Branch operands are logical entry
indices, converted to real word addresses by the actual jump transition. -/
def Instruction.encodeWords : Instruction → Vector Cell 5
  | .constant target value => ⟨#[.natural 0, registerWord target, value, .natural 0, .natural 0], rfl⟩
  | .move target source => ⟨#[.natural 1, registerWord target, registerWord source, .natural 0, .natural 0], rfl⟩
  | .loadInput target pointer => ⟨#[.natural 2, registerWord target, registerWord pointer, .natural 0, .natural 0], rfl⟩
  | .load target pointer => ⟨#[.natural 3, registerWord target, registerWord pointer, .natural 0, .natural 0], rfl⟩
  | .store pointer source => ⟨#[.natural 4, registerWord pointer, registerWord source, .natural 0, .natural 0], rfl⟩
  | .release pointer => ⟨#[.natural 5, registerWord pointer, .natural 0, .natural 0, .natural 0], rfl⟩
  | .natOp operation target left right =>
      ⟨#[.natural 6, .natural operation.word, registerWord target, registerWord left, registerWord right], rfl⟩
  | .ratOp operation target left right =>
      ⟨#[.natural 7, .natural operation.word, registerWord target, registerWord left, registerWord right], rfl⟩
  | .natCompare comparison target left right =>
      ⟨#[.natural 8, .natural comparison.word, registerWord target, registerWord left, registerWord right], rfl⟩
  | .ratCompare comparison target left right =>
      ⟨#[.natural 9, .natural comparison.word, registerWord target, registerWord left, registerWord right], rfl⟩
  | .natToRat target source => ⟨#[.natural 10, registerWord target, registerWord source, .natural 0, .natural 0], rfl⟩
  | .numeratorAbs target source => ⟨#[.natural 11, registerWord target, registerWord source, .natural 0, .natural 0], rfl⟩
  | .denominator target source => ⟨#[.natural 12, registerWord target, registerWord source, .natural 0, .natural 0], rfl⟩
  | .negative target source => ⟨#[.natural 13, registerWord target, registerWord source, .natural 0, .natural 0], rfl⟩
  | .branchZero condition whenZero whenNonzero =>
      ⟨#[.natural 14, registerWord condition, .natural whenZero, .natural whenNonzero, .natural 0], rfl⟩
  | .jump target => ⟨#[.natural 15, .natural target, .natural 0, .natural 0, .natural 0], rfl⟩
  | .jumpIndirect source => ⟨#[.natural 16, registerWord source, .natural 0, .natural 0, .natural 0], rfl⟩
  | .output source => ⟨#[.natural 17, registerWord source, .natural 0, .natural 0, .natural 0], rfl⟩
  | .halt => ⟨#[.natural 18, .natural 0, .natural 0, .natural 0, .natural 0], rfl⟩

def Instruction.decodeWords (words : Vector Cell 5) : Option Instruction := do
  let opcode ← words[0].nat?
  match opcode with
  | 0 => return .constant (← registerFromWord words[1]) words[2]
  | 1 => return .move (← registerFromWord words[1]) (← registerFromWord words[2])
  | 2 => return .loadInput (← registerFromWord words[1]) (← registerFromWord words[2])
  | 3 => return .load (← registerFromWord words[1]) (← registerFromWord words[2])
  | 4 => return .store (← registerFromWord words[1]) (← registerFromWord words[2])
  | 5 => return .release (← registerFromWord words[1])
  | 6 => return .natOp (← NatOp.fromWord (← words[1].nat?)) (← registerFromWord words[2]) (← registerFromWord words[3]) (← registerFromWord words[4])
  | 7 => return .ratOp (← RatOp.fromWord (← words[1].nat?)) (← registerFromWord words[2]) (← registerFromWord words[3]) (← registerFromWord words[4])
  | 8 => return .natCompare (← Comparison.fromWord (← words[1].nat?)) (← registerFromWord words[2]) (← registerFromWord words[3]) (← registerFromWord words[4])
  | 9 => return .ratCompare (← Comparison.fromWord (← words[1].nat?)) (← registerFromWord words[2]) (← registerFromWord words[3]) (← registerFromWord words[4])
  | 10 => return .natToRat (← registerFromWord words[1]) (← registerFromWord words[2])
  | 11 => return .numeratorAbs (← registerFromWord words[1]) (← registerFromWord words[2])
  | 12 => return .denominator (← registerFromWord words[1]) (← registerFromWord words[2])
  | 13 => return .negative (← registerFromWord words[1]) (← registerFromWord words[2])
  | 14 => return .branchZero (← registerFromWord words[1]) (← words[2].nat?) (← words[3].nat?)
  | 15 => return .jump (← words[1].nat?)
  | 16 => return .jumpIndirect (← registerFromWord words[1])
  | 17 => return .output (← registerFromWord words[1])
  | 18 => return .halt
  | _ => none

def encodeProgram (program : Program) : List Cell :=
  program.toList.flatMap (fun instruction => instruction.encodeWords.toList)

/-- Five actual readonly indexed reads, with all four offset additions
explicit in the transition's associated primitive trace. -/
def fetchInstruction (code : List Cell) (pc : ℕ) : Option Instruction := do
  let w0 ← code[pc]?
  let w1 ← code[pc + 1]?
  let w2 ← code[pc + 2]?
  let w3 ← code[pc + 3]?
  let w4 ← code[pc + 4]?
  Instruction.decodeWords ⟨#[w0, w1, w2, w3, w4], rfl⟩

def codeState (state : State) : State := { state with pc := 5 * state.pc }

def Instruction.executeCode (input : List Cell) (instruction : Instruction) (state : State) : Option State := do
  let after ← instruction.execute input state
  let pc := match instruction with
    | .branchZero _ _ _ | .jump _ | .jumpIndirect _ => 5 * after.pc
    | _ => state.pc + 5
  pure { after with pc := pc }

def codeStep (code : List Cell) (input : List Cell) (state : State) : Option State := do
  let instruction ← fetchInstruction code state.pc
  instruction.executeCode input state

def CodeRuns (code : List Cell) (input : List Cell) (trace : List State) (final : State) : Prop :=
  trace.head? = some initial ∧
    trace.IsChain (fun before after => codeStep code input before = some after) ∧
    trace.getLast? = some final ∧ fetchInstruction code final.pc = some .halt ∧
    final ∈ StateTransition.eval (codeStep code input) initial

def codePrimitiveTrace (code : List Cell) (trace : List State) : List Primitive :=
  trace.flatMap fun state => ((fetchInstruction code state.pc).map Instruction.primitives).getD []

/-- Coded fetch, complete runs including HALT, and exact actual fetched
primitive-trace correspondence are all conclusions to prove. Merely naming
solver labels or counting host Array iterations cannot discharge this target. -/
def CodeRefinementClaims : Prop :=
  (∀ instruction : Instruction, Instruction.decodeWords instruction.encodeWords = some instruction) ∧
    (∀ (program : Program) (pc : ℕ), fetchInstruction (encodeProgram program) (5 * pc) = program[pc]?) ∧
    (∀ (program : Program) (input : List Cell) (state : State),
      codeStep (encodeProgram program) input (codeState state) = (step program input state).map codeState) ∧
    (∀ (program : Program) (input : List Cell) (trace : List State) (final : State),
      Runs program input trace final → CodeRuns (encodeProgram program) input (trace.map codeState) (codeState final)) ∧
    (∀ (program : Program) (trace : List State),
      codePrimitiveTrace (encodeProgram program) (trace.map codeState) = primitiveTrace program trace) ∧
    ∀ program : Program, (encodeProgram program).length = 5 * program.size

def workingCells (state : State) : ℕ := state.live.card + registers.length + state.output.length

noncomputable def stateCellBits (state : State) : List ℕ :=
  (registers.map fun register => (state.register register).bits) ++
    (state.live.toList.flatMap fun address => [natBits address, (state.heap address).bits]) ++
      state.output.map Cell.bits ++ [natBits state.pc]

def peakCells (trace : List State) : ℕ := (trace.map workingCells).foldl max 0
noncomputable def peakOperandBits (trace : List State) : ℕ := (trace.flatMap stateCellBits).foldl max 0
def time (program : Program) (trace : List State) : ℕ := (primitiveTrace program trace).length

def encodeList {α : Type*} (encode : α → List Cell) (values : List α) : List Cell :=
  .natural values.length :: values.flatMap encode

def encodeAction : MenuAction → List Cell
  | .finish => [.natural 0]
  | .abandon => [.natural 1]
  | .test level bad => [.natural 2, .natural level, .natural (if bad = .repair then 1 else 0)]

def encodeEntry (entry : MenuEntry) : List Cell :=
  encodeAction entry.action ++ [.rational entry.observation, .rational entry.repairs, .rational entry.failure]

def encodeRow (row : MenuRow) : List Cell := encodeList encodeEntry row.toList
def encodeTable (table : MenuTable) : List Cell := encodeList encodeRow table.toList
def encodeSolve (solution : MultiplierSolve) : List Cell := .rational solution.multiplier :: encodeTable solution.table

def encodeState : MultiplierState → List Cell
  | .exact solution => .natural 0 :: encodeSolve solution
  | .bracket lower upper => .natural 1 :: encodeSolve lower ++ encodeSolve upper

def encodeEndpoint (endpoint : EndpointConstant) : List Cell := [.rational endpoint.error, .rational endpoint.charge]
def encodeCalibration (calibration : CalibrationConstant) : List Cell := [.rational calibration.error, .rational calibration.weight]

def encodeFrontend (frontend : CachedFrontend) : List Cell :=
  encodeList encodeEndpoint frontend.endpoints.toList ++
    encodeList encodeCalibration frontend.calibrationWeights.toList ++ encodeState frontend.state

def readNat : List Cell → Option (ℕ × List Cell)
  | .natural value :: rest => some (value, rest)
  | _ => none

def readRat : List Cell → Option (ℚ × List Cell)
  | .rational value :: rest => some (value, rest)
  | _ => none

def readMany {α : Type} (read : List Cell → Option (α × List Cell)) : ℕ → List Cell → Option (List α × List Cell)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (value, rest) ← read input
      let (values, tail) ← readMany read count rest
      pure (value :: values, tail)

def readList {α : Type} (read : List Cell → Option (α × List Cell)) (input : List Cell) : Option (List α × List Cell) := do
  let (count, rest) ← readNat input
  readMany read count rest

def readAction (input : List Cell) : Option (MenuAction × List Cell) := do
  let (tag, rest) ← readNat input
  if tag = 0 then pure (.finish, rest) else if tag = 1 then pure (.abandon, rest)
  else if tag = 2 then
    let (level, rest) ← readNat rest
    let (bad, rest) ← readNat rest
    if bad = 0 then pure (.test level .abandon, rest)
    else if bad = 1 then pure (.test level .repair, rest) else none
  else none

def readEntry (input : List Cell) : Option (MenuEntry × List Cell) := do
  let (action, rest) ← readAction input
  let (observation, rest) ← readRat rest
  let (repairs, rest) ← readRat rest
  let (failure, rest) ← readRat rest
  pure (⟨action, observation, repairs, failure⟩, rest)

def readRow (input : List Cell) : Option (MenuRow × List Cell) := do
  let (entries, rest) ← readList readEntry input
  pure (entries.toArray, rest)

def readTable (input : List Cell) : Option (MenuTable × List Cell) := do
  let (rows, rest) ← readList readRow input
  pure (rows.toArray, rest)

def readSolve (input : List Cell) : Option (MultiplierSolve × List Cell) := do
  let (multiplier, rest) ← readRat input
  let (table, rest) ← readTable rest
  pure (⟨multiplier, table⟩, rest)

def readState (input : List Cell) : Option (MultiplierState × List Cell) := do
  let (tag, rest) ← readNat input
  let (lower, rest) ← readSolve rest
  if tag = 0 then pure (.exact lower, rest) else if tag = 1 then
    let (upper, rest) ← readSolve rest
    pure (.bracket lower upper, rest)
  else none

def readEndpoint (input : List Cell) : Option (EndpointConstant × List Cell) := do
  let (error, rest) ← readRat input
  let (charge, rest) ← readRat rest
  pure (⟨error, charge⟩, rest)

def readCalibration (input : List Cell) : Option (CalibrationConstant × List Cell) := do
  let (error, rest) ← readRat input
  let (weight, rest) ← readRat rest
  pure (⟨error, weight⟩, rest)

def readFrontend (input : List Cell) : Option (CachedFrontend × List Cell) := do
  let (endpoints, rest) ← readList readEndpoint input
  let (calibration, rest) ← readList readCalibration rest
  let (state, rest) ← readState rest
  pure (⟨endpoints.toArray, calibration.toArray, state⟩, rest)

def decodeFrontend (input : List Cell) : Option CachedFrontend := do
  let (frontend, rest) ← readFrontend input
  if rest = [] then pure frontend else none

def clipRat (value : ℚ) : ℚ := max 0 (min 1 value)

def selectorWeightRat (P : PaperProofs.Paid.Parameters) (fee : ℚ) (frontend : CachedFrontend) : ℚ :=
  if P.zeroChargeRisk fee ≤ P.certificate.risk then 0 else match frontend.state with
    | .exact _ => 0
    | .bracket lower upper => clipRat (P.mixtureWeight lower upper)

/-- Compact output also stores the original one-time whole-policy selector
weight. Calibration weights remain in the frontend's original cache. -/
structure Artifact where
  frontend : CachedFrontend
  selectorWeight : ℚ

def buildArtifact (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Artifact :=
  let frontend := P.buildCachedFrontend fee
  ⟨frontend, selectorWeightRat P fee frontend⟩

def encodeArtifact (artifact : Artifact) : List Cell :=
  encodeFrontend artifact.frontend ++ [.rational artifact.selectorWeight]

def decodeArtifact (input : List Cell) : Option Artifact := do
  let (frontend, rest) ← readFrontend input
  let (weight, rest) ← readRat rest
  if rest = [] then pure ⟨frontend, weight⟩ else none

/-- Ordinary sign/magnitude numerator and denominator encoding. The unary
length prefix is linear in the binary length, not in the encoded number. -/
def encodeNatBits (value : ℕ) : List Bool :=
  List.replicate (natBits value) true ++ [false] ++
    List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)

def encodeCellBits : Cell → List Bool
  | .natural value => false :: encodeNatBits value
  | .rational value => [true, decide (value < 0)] ++ encodeNatBits value.num.natAbs ++ encodeNatBits value.den

/-- A final true delimiter avoids Boolean TM blank-tail identification. -/
def encodeBits (input : List Cell) : List Bool :=
  encodeNatBits input.length ++ input.flatMap encodeCellBits ++ [true]

theorem halt_time : time #[.halt] [initial] = 11 := rfl

theorem halt_peakCells : peakCells [initial] = 7 := rfl

theorem halt_runs : Runs #[.halt] [] [initial] initial := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · simp
  · exact StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, rfl⟩

def CodecClaims : Prop :=
  (∀ frontend : CachedFrontend, decodeFrontend (encodeFrontend frontend) = some frontend) ∧
    (∀ artifact : Artifact, decodeArtifact (encodeArtifact artifact) = some artifact) ∧
    ∃ C : ℕ, 0 < C ∧ ∀ cell : Cell, (encodeCellBits cell).length ≤ C * cell.bits

/-- The raw input includes exactly original N,K,gamma,delta,c,f. Derived
certificate integers, endpoints, calibration values, tables and traces are
ABSENT. A single uniform preparation program must compute them. -/
def rawInput (P : PaperProofs.Paid.Parameters) (fee : ℚ) : List Cell :=
  [.natural P.certificate.stages, .natural P.tools, .rational P.certificate.gamma,
    .rational P.certificate.risk, .rational P.reviewFee, .rational fee]

def preparedInput (P : PaperProofs.Paid.Parameters) (fee : ℚ) : List Cell :=
  rawInput P fee ++ [.natural P.certificate.t0, .natural P.certificate.M,
    .natural P.certificate.E, .natural P.certificate.Q, .natural (P.bisectionBudget fee),
    .rational P.Lambda, .rational (P.zeroChargeRisk fee)]

/-- This per-solve readonly cache is charged once by the full core program,
whose own input has no endpoint data. It is not a free endpoint oracle. -/
def solveInput (P : PaperProofs.Paid.Parameters) (fee penalty : ℚ) (n k : ℕ) : List Cell :=
  [.natural n, .natural k, .natural P.certificate.M, .rational fee, .rational penalty] ++
    encodeList encodeEndpoint P.endpointCache.toList

def calibrationInput (P : PaperProofs.Paid.Parameters) : List Cell :=
  [.natural P.certificate.M, .natural P.certificate.Q, .rational P.certificate.gamma] ++
    encodeList encodeEndpoint P.endpointCache.toList

def sourceCoreScale (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  (P.bisectionBudget fee + 2) * (P.certificate.stages + 1) * (P.tools + 1) * (P.certificate.M + 1) +
    P.certificate.Q * (P.certificate.M + 1)^2

def sourceRecordSpace (P : PaperProofs.Paid.Parameters) : ℕ :=
  (P.certificate.stages + 1) * (P.tools + 1) + (P.certificate.M + 1)

def rawSize (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  P.certificate.stages + natBits P.tools + ratEncodingBits P.certificate.risk +
    ratEncodingBits P.reviewFee + ratEncodingBits fee + 1

def variableGammaSize (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  rawSize P fee + ratEncodingBits P.certificate.gamma + ⌈P.certificate.gamma⁻¹⌉₊ + 1

def maximumMenuBits (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  ((P.menuScalars fee).map ratEncodingBits).foldl max 1

/-- Includes numerator magnitude, index/address words, every dyadic
multiplier, and calibration operands, not just final-table denominators. -/
def coreOperandBound (P : PaperProofs.Paid.Parameters) (fee : ℚ) : ℕ :=
  (P.certificate.stages + 1) * (2 * (P.certificate.M + 1) + 2) * (maximumMenuBits P fee + 1) +
    (P.certificate.Q + 1) * (ratEncodingBits P.certificate.gamma + 2) +
    (P.bisectionBudget fee + 1) * (ratEncodingBits P.Lambda + ratEncodingBits P.certificate.risk + 1) +
    rawSize P fee + natBits P.certificate.M + natBits P.certificate.Q + 1

structure RoutineLabels where
  solveEntry : ℕ
  solveReturn : ℕ
  endpointEntry : ℕ
  calibrationEntry : ℕ

def entryCount (pc : ℕ) (trace : List State) : ℕ :=
  (trace.filter (fun state => state.pc == pc)).length

/-- These requests are read from real reached RAM registers at a real code
entry address. They are separate from the primitive-time measurement. -/
def actualSolveRequests (labels : RoutineLabels) (trace : List State) : List ℚ :=
  trace.filterMap fun state => if state.pc = labels.solveEntry then (state.register .total).rat? else none

def heapSegment (state : State) (base count : ℕ) : List Cell :=
  (List.range count).map fun offset => state.heap (base + offset)

/-- Every actual solver entry has a real return with the exact original
table in live heap cells. A label alone never certifies a solve or its cost. -/
def SolverCallRefinement (program : Program) (labels : RoutineLabels)
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (constant : ℕ) (states : List State) : Prop :=
  ∀ index state, states[index]? = some state → state.pc = labels.solveEntry →
    ∃ multiplier : ℚ, (state.register .total).rat? = some multiplier ∧
      ∃ later final base, index < later ∧ states[later]? = some final ∧ final.pc = labels.solveReturn ∧
        (final.register .address).nat? = some base ∧
        let table := P.cachedSolveMenuTable P.endpointCache fee multiplier P.tools P.certificate.stages
        (∀ offset < (encodeTable table).length, base + offset ∈ final.live) ∧
        heapSegment final base (encodeTable table).length = encodeTable table ∧
        time program ((states.drop index).take (later - index + 1)) ≤
          constant * (P.certificate.stages + 1) * (P.tools + 1) * (P.certificate.M + 1)

/-- Full literal rational-RAM obligations, including raw certificate
preparation. All four programs and constants precede ALL inputs. A solve
and calibration have their stated numerical operation/space bounds. The
full core computes/stores the original cached frontend, logs the exact
source solve requests at genuine solver calls, calibrates once, and retains
only a constant number of endpoint tables plus O(M) caches/temporary rows.
Program text and readonly input are counted separately from live records. -/
def UniformRationalImplementationClaims : Prop :=
  ∃ (prepare solver calibrate core : Program) (labels : RoutineLabels)
    (Ctime Cspace Cbits Cprepare degree : ℕ),
    0 < Ctime ∧ 0 < Cspace ∧ 0 < Cbits ∧ 0 < Cprepare ∧
    ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ), 0 ≤ fee →
      (∃ trace final, Runs prepare (rawInput P fee) trace final ∧ final.output = preparedInput P fee ∧
        time prepare trace ≤ Cprepare * (variableGammaSize P fee)^degree ∧
        peakCells trace ≤ Cprepare * (variableGammaSize P fee)^degree ∧
        peakOperandBits trace ≤ Cprepare * (variableGammaSize P fee)^degree) ∧
      (∀ (penalty : ℚ) (n k : ℕ), ∃ trace final,
        Runs solver (solveInput P fee penalty n k) trace final ∧
        final.output = encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n) ∧
        time solver trace ≤ Ctime * (n + 1) * (k + 1) * (P.certificate.M + 1) ∧
        peakCells trace ≤ Cspace * (n + 1) * (k + 1) ∧
        peakOperandBits trace ≤ Cbits * ((n + 1) * (2 * (P.certificate.M + 1) + 2) *
          (maximumMenuBits P fee + 1) + ratEncodingBits penalty + natBits n + natBits k + 1)) ∧
      (∃ trace final, Runs calibrate (calibrationInput P) trace final ∧
        final.output = encodeList encodeCalibration (P.calibrationWeightCache P.endpointCache).toList ∧
        time calibrate trace ≤ Ctime * P.certificate.Q * (P.certificate.M + 1)^2 ∧
        peakCells trace ≤ Cspace * (P.certificate.M + 1) ∧
        peakOperandBits trace ≤ Cbits * ((P.certificate.Q + 1) *
          (ratEncodingBits P.certificate.gamma + 2) + maximumMenuBits P fee + 1)) ∧
      ∃ trace final, Runs core (preparedInput P fee) trace final ∧
        decodeArtifact final.output = some (buildArtifact P fee) ∧
        final.output = encodeArtifact (buildArtifact P fee) ∧
        time core trace ≤ Ctime * sourceCoreScale P fee ∧
        peakCells trace ≤ Cspace * sourceRecordSpace P ∧
        peakOperandBits trace ≤ Cbits * coreOperandBound P fee ∧
        actualSolveRequests labels trace = (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 ∧
        entryCount labels.solveEntry trace = (actualSolveRequests labels trace).length ∧
        entryCount labels.solveEntry trace ≤ P.bisectionBudget fee + 2 ∧
        entryCount labels.endpointEntry trace = 1 ∧ entryCount labels.calibrationEntry trace = 1 ∧
        SolverCallRefinement core labels P fee Ctime trace

abbrev BitMachine (states : ℕ) := Turing.TM0.Machine Bool (Fin (states + 1))
abbrev BitState (states : ℕ) := Turing.TM0.Cfg Bool (Fin (states + 1))

def BitRuns {states : ℕ} (machine : BitMachine states) (input : List Bool)
    (trace : List (BitState states)) (final : BitState states) : Prop :=
  trace.head? = some (Turing.TM0.init input) ∧
    trace.IsChain (fun before after => Turing.TM0.step machine before = some after) ∧
    trace.getLast? = some final ∧ Turing.TM0.step machine final = none ∧
    final ∈ StateTransition.eval (Turing.TM0.step machine) (Turing.TM0.init input)

def headMovement {states : ℕ} (machine : BitMachine states) (state : BitState states) : ℤ :=
  match machine state.q state.Tape.head with
  | some (_, .move .left) => -1
  | some (_, .move .right) => 1
  | _ => 0

/-- Actual tape-head displacements recover visited space even though the
official TM0 configuration records a relative tape. Input cells are included. -/
def visitedBitSpace {states : ℕ} (machine : BitMachine states) (inputLength : ℕ)
    (trace : List (BitState states)) : ℕ :=
  let positions := (trace.map (headMovement machine)).scanl (· + ·) 0
  let high := positions.foldl max (inputLength : ℤ)
  let low := positions.foldl min 0
  (high - low).toNat + 1

/-- A single genuine finite-control Bool TM computes the exact fixed
frontend from RAW input, with no rational unit-cost oracle. Its actual
transition count and visited-bit space are polynomial for fixed rational
gamma and in explicit numerical 1/gamma when gamma varies. The fee's full
encoding, however small positive f is, is included in every bound.
No private-coin sampling-time bound is included in this OFFLINE target. -/
def UniformBitImplementationClaims : Prop :=
  ∃ (states : ℕ) (machine : BitMachine states),
    (∀ gamma : ℚ, 0 < gamma → gamma ≤ 1 / 4 → ∃ C degree : ℕ, 0 < C ∧
      ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ), P.certificate.gamma = gamma → 0 ≤ fee →
        ∃ trace final, BitRuns machine (encodeBits (rawInput P fee)) trace final ∧
          final.Tape.right₀ = Turing.ListBlank.mk (encodeBits (encodeArtifact (buildArtifact P fee))) ∧
          trace.length ≤ C * (rawSize P fee)^degree ∧
          visitedBitSpace machine (encodeBits (rawInput P fee)).length trace ≤ C * (rawSize P fee)^degree) ∧
    ∃ C degree : ℕ, 0 < C ∧ ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ), 0 ≤ fee →
      ∃ trace final, BitRuns machine (encodeBits (rawInput P fee)) trace final ∧
        final.Tape.right₀ = Turing.ListBlank.mk (encodeBits (encodeArtifact (buildArtifact P fee))) ∧
        trace.length ≤ C * (variableGammaSize P fee)^degree ∧
        visitedBitSpace machine (encodeBits (rawInput P fee)).length trace ≤ C * (variableGammaSize P fee)^degree

abbrev FairTape := ℕ → Bool

noncomputable def fairTapeLaw : Measure FairTape :=
  Measure.infinitePi fun _ : ℕ => Statistics.BinarySymmetric.Parameters.fairGuessLaw

instance fairTapeLaw_probability : IsProbabilityMeasure fairTapeLaw := by
  unfold fairTapeLaw
  infer_instance

structure CoinState where
  accumulator : ℕ
  filled : ℕ
  bitsRead : ℕ
  result : Option Bool
  deriving DecidableEq

def coinInitial : CoinState := ⟨0, 0, 0, none⟩

def coinWidth (probability : Set.Icc (0 : ℚ) 1) : ℕ := natBits probability.val.den

/-- Literal private fair-bit rejection sampler. Build an unsigned width-bit
integer; accept below the rational denominator and compare with its numerator,
otherwise restart the block. Endpoints use no bits. A rejected block consumes
its bits; there is no bounded-bit completion or rational-coin oracle. -/
def coinStep (probability : Set.Icc (0 : ℚ) 1) (tape : FairTape) (state : CoinState) : Option CoinState :=
  if state.result.isSome then none else if probability.val = 0 then
    some { state with result := some false }
  else if probability.val = 1 then some { state with result := some true }
  else if state.filled < coinWidth probability then
    let bit := if tape state.bitsRead then 1 else 0
    some { state with
      accumulator := 2 * state.accumulator + bit
      filled := state.filled + 1
      bitsRead := state.bitsRead + 1 }
  else if state.accumulator < probability.val.den then
    some { state with result := some (decide (state.accumulator < probability.val.num.toNat)) }
  else some { state with accumulator := 0, filled := 0 }

def coinRun (probability : Set.Icc (0 : ℚ) 1) (tape : FairTape) : ℕ → CoinState
  | 0 => coinInitial
  | steps + 1 =>
    let previous := coinRun probability tape steps
    (coinStep probability tape previous).getD previous

noncomputable def coinResult (probability : Set.Icc (0 : ℚ) 1) (tape : FairTape) : Option Bool := by
  classical
  exact if h : ∃ steps, (coinRun probability tape steps).result.isSome = true
    then (coinRun probability tape (Nat.find h)).result else none

noncomputable def coinBits (probability : Set.Icc (0 : ℚ) 1) (tape : FairTape) : ℕ∞ := by
  classical
  exact if h : ∃ steps, (coinRun probability tape steps).result.isSome = true
    then ((coinRun probability tape (Nat.find h)).bitsRead : ℕ∞) else ⊤

def realProbability (probability : Set.Icc (0 : ℚ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨(probability.val : ℝ), by
    constructor
    · exact_mod_cast probability.property.1
    · exact_mod_cast probability.property.2⟩

def rationalProbability (value : ℚ) : Set.Icc (0 : ℚ) 1 :=
  ⟨clipRat value, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

instance : MeasurableSpace (Option Bool) := ⊤
instance : MeasurableSingletonClass (Option Bool) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Original D:641--642 only: ordinary private bits suffice, the sampler is
causal, nonreturn is null, and its returned law is the exact rational coin.
There is intentionally no worst-case or expected sampling-bit/time bound.
This pending theorem is not an assumption of any policy or value definition. -/
def ExactRationalCoinClaims : Prop :=
  ∀ probability : Set.Icc (0 : ℚ) 1,
    Measurable (coinResult probability) ∧
    fairTapeLaw {tape | coinResult probability tape = none} = 0 ∧
    fairTapeLaw.map (coinResult probability) =
      (Statistics.BinarySymmetric.Parameters.rocCoinLaw (realProbability probability)).map some ∧
    ∀ (tape tape' : FairTape) (count : ℕ),
      (∀ k < count, tape k = tape' k) → coinBits probability tape ≤ (count : ℕ∞) →
        coinResult probability tape' = coinResult probability tape

abbrev CoinIndex (P : PaperProofs.Paid.Parameters) :=
  Unit ⊕ (P.sharedInstance.Stage ⊕ (P.sharedInstance.Stage × Fin (P.certificate.M + 1)))

abbrev PrivateStreams (P : PaperProofs.Paid.Parameters) := CoinIndex P → FairTape

noncomputable def privateStreamsLaw (P : PaperProofs.Paid.Parameters) : Measure (PrivateStreams P) :=
  Measure.pi fun _ : CoinIndex P => fairTapeLaw

instance privateStreamsLaw_probability (P : PaperProofs.Paid.Parameters) : IsProbabilityMeasure (privateStreamsLaw P) := by
  unfold privateStreamsLaw
  infer_instance

def selectorProbability (P : PaperProofs.Paid.Parameters) (fee : ℚ) : Set.Icc (0 : ℚ) 1 :=
  rationalProbability (buildArtifact P fee).selectorWeight

def calibrationProbability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (level : Fin (P.certificate.M + 1)) :
    Set.Icc (0 : ℚ) 1 :=
  rationalProbability (P.cachedCalibrationWeight (buildArtifact P fee).frontend.calibrationWeights level.val)

noncomputable def sampledSeed (P : PaperProofs.Paid.Parameters) (fee : ℚ) (streams : PrivateStreams P) :
    P.CalibratedSearchSeed :=
  ((coinResult (selectorProbability P fee) (streams (.inl ()))).getD false,
    (fun stage => (coinResult (rationalProbability (1 / 2)) (streams (.inr (.inl stage)))).getD false),
    fun stage level => (coinResult (calibrationProbability P fee level) (streams (.inr (.inr (stage, level))))).getD false)

def seedSamplerReturns (P : PaperProofs.Paid.Parameters) (fee : ℚ) (streams : PrivateStreams P) : Prop :=
  (coinResult (selectorProbability P fee) (streams (.inl ()))).isSome = true ∧
    (∀ stage, (coinResult (rationalProbability (1 / 2)) (streams (.inr (.inl stage)))).isSome = true) ∧
    ∀ stage level, (coinResult (calibrationProbability P fee level) (streams (.inr (.inr (stage, level))))).isSome = true

/-- Actual finite-family sampler for THIS cached algorithm's whole-policy
selector, fair stage bits and independent stage/level marks. It receives only
private fair tapes, no Native.World and no observation/correction interface.
The default on a nonreturned coin is only an explicit total completion; its
exceptional event must be proved null, not silently deleted from native fees.
This is a seed-law identity, not a new delta-safety or cost guarantee. -/
def PrivateSeedSamplingClaims : Prop :=
  ∀ (P : PaperProofs.Paid.Parameters) (fee : ℚ), 0 ≤ fee →
    Measurable (sampledSeed P fee) ∧
    privateStreamsLaw P {streams | ¬ seedSamplerReturns P fee streams} = 0 ∧
    (privateStreamsLaw P).map (sampledSeed P fee) = P.cachedAlgorithmSeedLaw fee

/-- Full first-round D27 target. Every conjunct remains an obligation.
Actual RAM/TM runs, live storage, all intermediate bit sizes and private
sampling are now separate explicit interfaces. Existing bit/data targets
remain conclusions here; none is assumed as a qualification of an input. -/
def ComputationalClaims : Prop :=
  CodecClaims ∧ CodeRefinementClaims ∧ UniformRationalImplementationClaims ∧ UniformBitImplementationClaims ∧
    ExactRationalCoinClaims ∧ PrivateSeedSamplingClaims ∧
    ∀ P : PaperProofs.Paid.Parameters, P.CachedDataBitClaims

end PaperProofs.Paid.Computation
