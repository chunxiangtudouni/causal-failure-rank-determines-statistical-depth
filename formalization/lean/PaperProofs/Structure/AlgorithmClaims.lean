module

public import PaperProofs.Structure.RawClosureRAM
public import PaperProofs.Structure.IndexedUsedCounts
public import PaperProofs.Structure.IndexedQuery
public import PaperProofs.Structure.ControllerBoundaries
public import Mathlib.Data.Nat.Log

/-!
Pending A17 implementation claim, on the frozen paper's *given tree* input.

This file is a specification, not a proof of the algorithmic theorem.  The
already verified closure/count/query components do not prove this claim.
In particular the code below does not treat a cell, row, support lookup,
set cardinality, rank, or descent as one RAM instruction.

The same program is selected from N,q,t before every raw incidence input,
tree contents, query stage, and used bitmap.  The logical instructions are
the existing encoded seven-register RAM instructions (including saturating
subtraction).  No cardinality/internal cache, leaf-tool lookup, capacity
table, stage-node lookup, used-count array, rank, tool answer, or precomputed
execution trace occurs in the raw ROM.

The explicit incidence construction/check in A06 and the q=0 direct case
in A18 remain separate premises when assembling A19.  A17 here includes
the entire table construction, raw-bitmap query, two-layer variant, physical
code/ROM loading, finite-word safety, and actual along-execution traces.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.AlgorithmClaims

open IndexedRAM IndexedClosureRAM IndexedEntry

variable {bits : Nat}

/-- Physical ROM regions: actual finite words, not an arbitrary oracle. -/
structure PhysicalROM where
  input : List Nat
  internal : List Nat
  children : List Nat

def PhysicalROM.words (rom : PhysicalROM) : Region → List Nat
  | .input => rom.input
  | .internal => rom.internal
  | .children => rom.children

def PhysicalROM.semantic (rom : PhysicalROM) : ROM :=
  ⟨fun region address => (rom.words region).getD address 0⟩

def PhysicalROM.size (rom : PhysicalROM) : Nat :=
  rom.input.length + rom.internal.length + rom.children.length

def bit (value : Bool) : Nat := if value then 1 else 0

def incidence {q : Nat} (full : List (Finset (Fin q))) : List Nat :=
  full.flatMap (fun eligible => (List.finRange q).map (fun tool => bit (decide (tool ∈ eligible))))

/-- The given tree supplies node incidences and parent/adjacency only.
Cardinalities, internal flags, leaf labels and stage-node matching must be
computed by the implementation.  Zero encodes the absent parent. -/
def givenTreeROM (q : Nat) (full : List (Finset (Fin q))) : PhysicalROM :=
  let cache := (prepareNormalization q full).indexed
  let nodes := List.finRange cache.nodes.size
  { input := [full.length, q, cache.nodes.size] ++ incidence full ++
      nodes.flatMap (fun node => (List.finRange q).map
        (fun tool => bit (decide (tool ∈ cache.decode node))))
    internal := (nodes.map (fun node => IndexedClosureRAM.encodedNode cache (cache.parents.get node))) ++
      (nodes.map (fun node => (cache.children.get node).size))
    children := nodes.flatMap (fun node => (cache.children.get node).toList.map Fin.val) }

def queryROM (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) : PhysicalROM :=
  let tree := givenTreeROM q full
  { tree with input := tree.input ++ [stage] ++
      (List.finRange q).map (fun tool => bit (decide (tool ∈ used))) }

/-- A word RAM address may include polynomially many table/code words;
a constant multiple of log(N+q+2) bits therefore suffices. -/
def indexWidth (factor N q : Nat) : Nat := factor * Nat.clog 2 (N + q + 2)

def Fits (bits value : Nat) : Prop := value < 2 ^ bits

def WordsFit (bits : Nat) (words : List Nat) : Prop := ∀ value ∈ words, Fits bits value

def StateFits (bits heapWords : Nat) (state : State) : Prop :=
  Fits bits (state.pc + 4) ∧
    (∀ register, Fits bits (state.register register)) ∧
    (∀ address < heapWords, Fits bits (state.heap address))

/-- Every actual memory access is in its physical allocated region. -/
def AccessFits (rom : PhysicalROM) (heapWords : Nat) (state : State) : Op → Prop
  | .subtract _ _ _ => True
  | .base (.loadROM region _ pointer) => state.register pointer < (rom.words region).length
  | .base (.loadHeap _ pointer) => state.register pointer < heapWords
  | .base (.storeHeap pointer _) => state.register pointer < heapWords
  | .base _ => True

/-- Safety is checked at every actual instruction prefix, rather than just
for the final capacities.  It includes PC/addresses, transient sums, code
immediates, ROM words, and every writable memory word. -/
def FiniteSafe (bits heapWords : Nat) (rom : PhysicalROM) (program : List Op)
    (initial : State) : Prop :=
  WordsFit bits (haltingWords program) ∧
    (∀ region, WordsFit bits (rom.words region)) ∧
    Fits bits (rom.size + heapWords + (haltingWords program).length) ∧
    (∀ count ≤ program.length,
      StateFits bits heapWords (execute rom.semantic (program.take count) initial)) ∧
    (∀ count (hcount : count < program.length),
      AccessFits rom heapWords (execute rom.semantic (program.take count) initial) program[count])

/-- Real fixed-width state used by the implementation-refinement target. -/
structure WordState (bits : Nat) where
  register : Register → BitVec bits
  heap : BitVec bits → BitVec bits
  pc : BitVec bits
  halted : Bool

def wordState (bits : Nat) (state : State) : WordState bits :=
  { register := fun register => BitVec.ofNat bits (state.register register)
    heap := fun address => BitVec.ofNat bits (state.heap address.toNat)
    pc := BitVec.ofNat bits state.pc
    halted := false }

def wordInstruction (rom : PhysicalROM) (instruction : Instruction) (state : WordState bits) : WordState bits :=
  let registers := state.register
  let after := match instruction with
    | .constant target value => { state with register := Function.update registers target (BitVec.ofNat bits value) }
    | .add target left right => { state with register := Function.update registers target (registers left + registers right) }
    | .minimum target left right =>
      { state with
        register := Function.update registers target
          (if (registers left).toNat ≤ (registers right).toNat then registers left else registers right) }
    | .select target condition whenTrue whenFalse =>
      { state with
        register := Function.update registers target
          (if (registers condition).toNat = 0 then registers whenFalse else registers whenTrue) }
    | .loadROM region target pointer =>
      { state with
        register := Function.update registers target
          (BitVec.ofNat bits ((rom.words region).getD (registers pointer).toNat 0)) }
    | .loadHeap target pointer => { state with register := Function.update registers target (state.heap (registers pointer)) }
    | .storeHeap pointer source => { state with heap := Function.update state.heap (registers pointer) (registers source) }
  { after with pc := state.pc + BitVec.ofNat bits 5 }

def wordOp (rom : PhysicalROM) : Op → WordState bits → WordState bits
  | .base instruction, state => wordInstruction rom instruction state
  | .subtract target left right, state =>
    { state with
      register := Function.update state.register target
          (BitVec.ofNat bits ((state.register left).toNat - (state.register right).toNat))
      pc := state.pc + BitVec.ofNat bits 5 }

/-- Fetch/decode uses the same five-word opcode decoder as the Nat RAM.
The fetched code words themselves are physically truncated BitVec words. -/
def wordStep (rom : PhysicalROM) (code : List (BitVec bits)) (state : WordState bits) : WordState bits :=
  if state.halted then state else
    let fetched : Vector Nat 5 := Vector.ofFn (fun position =>
      ((code.getD (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)
    match Op.decodeWords fetched with
    | none => { state with halted := true }
    | some op => wordOp rom op state

def wordRun (rom : PhysicalROM) (code : List (BitVec bits)) : Nat → WordState bits → WordState bits
  | 0, state => state
  | count + 1, state => wordRun rom code count (wordStep rom code state)

def WordRefines (bits : Nat) (rom : PhysicalROM) (program : List Op) (initial : State) : Prop :=
  let code := (haltingWords program).map (BitVec.ofNat bits)
  (∀ count ≤ program.length,
    wordRun rom code count (wordState bits initial) =
      wordState bits (execute rom.semantic (program.take count) initial)) ∧
    wordRun rom code (program.length + 1) (wordState bits initial) =
      { wordState bits (execute rom.semantic program initial) with halted := true }

def initial (heap : Nat → Nat) : State := ⟨fun _ => 0, heap, 0⟩

def cells (N q : Nat) : Nat := (N + 1) * (q + 2)

/-- Fixed tagged slots; every entry has its own physical tag. -/
def tableWords (N q t : Nat) : Nat := cells N q * (t + 1)

def readEntry (t slot : Nat) (heap : Nat → Nat) : CapacityBits.Entry t :=
  if heap (slot * (t + 1)) = 0 then .void else
    .vector (Vector.ofFn (fun node => heap (slot * (t + 1) + 1 + node.val)))

def PhysicalTableCorrect (q : Nat) (full : List (Finset (Fin q))) (heap : Nat → Nat) : Prop :=
  let cache := (prepareNormalization q full).indexed
  (∀ stage : Fin (full.length + 1), ∀ budget : Fin (q + 2),
    readEntry cache.nodes.size (stage.val * (q + 2) + budget.val) heap =
      (IndexedQuery.storedPositiveRow q full stage).get budget) ∧
  (∀ slot < cells full.length q, heap (slot * (cache.nodes.size + 1)) ≤ 1)

def encodeRank (q : Nat) (rank : ℕ∞) : Nat := if rank = ⊤ then q + 2 else rank.toNat

def expectedReply (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) : IndexedQuery.Reply q :=
  if h : stage.val < full.length then
    let current : Fin full.length := ⟨stage.val, h⟩
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    let cache := (prepareNormalization q full).indexed
    IndexedQuery.query cache (IndexedDescent.leafTools cache) (IndexedDescent.usedCounts cache used)
      (IndexedQuery.storedPositiveRow q full next) (IndexedQuery.storedStageNode q full hq current)
  else IndexedQuery.terminalReply q

theorem expectedReply_rank (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    (expectedReply q full hq stage used).rank = errorRank (full.drop stage.val) (Finset.univ \ used) := by
  by_cases hstage : stage.val < full.length
  · simpa only [expectedReply, hstage, ↓reduceDIte] using
      IndexedQuery.stored_query_rank q full hq hlaminar used ⟨stage.val, hstage⟩
  · have heq : stage.val = full.length := by omega
    rw [expectedReply, dite_eq_right hstage]
    change (⊤ : ℕ∞) = errorRank (full.drop stage.val) (Finset.univ \ used)
    rw [heq, List.drop_length, errorRank_terminal]

def ReplyCorrect (q : Nat) (answer : IndexedQuery.Reply q) (state : State) : Prop :=
  state.register .value = encodeRank q answer.rank ∧
    state.register .old = encodeRank q answer.good ∧
    state.register .fresh = encodeRank q answer.bad ∧
    state.register .index = (match answer.tool with | none => 0 | some tool => tool.val + 1)

/-- A physical implementation contains executable code/layout only.  No
correctness, cost, trace, or target output is supplied as an input field. -/
structure Implementation where
  buildProgram : Nat → Nat → Nat → List Op
  queryProgram : Nat → Nat → Nat → List Op
  rollingProgram : Nat → Nat → Nat → List Op
  capacityWords : Nat → Nat → Nat → Nat
  indexWords : Nat → Nat → Nat → Nat
  rollingCapacityWords : Nat → Nat → Nat → Nat
  rollingIndexWords : Nat → Nat → Nat → Nat

def work (N q t : Nat) : Nat := (N + 1) * (q + 1) * t

def queryWork (q t : Nat) : Nat := (q + 1) * t

/-- Code and physical ROM loading each cost one word operation per word;
initial register/PC setup costs eight writes. Workspace zero-initialization
is charged here as well. Execution includes the encoded terminal HALT. -/
def totalBuildCost (rom : PhysicalROM) (program : List Op) (heapWords : Nat) : Nat :=
  rom.size + (haltingWords program).length + heapWords + 8 + (trace program ++ haltTrace).length

def totalQueryCost (q : Nat) (program : List Op) : Nat :=
  (q + 1) + (haltingWords program).length + 8 + (trace program ++ haltTrace).length

def CapacityPrefixBounded (q words : Nat) (heap : Nat → Nat) : Prop :=
  ∀ address < words, heap address ≤ q

def CapacityThroughout (q capWords : Nat) (rom : PhysicalROM) (program : List Op) (start : State) : Prop :=
  ∀ count ≤ program.length,
    CapacityPrefixBounded q capWords (execute rom.semantic (program.take count) start).heap

def ExecutionClaims (wordFactor N q : Nat) (heapWords : Nat) (rom : PhysicalROM)
    (program : List Op) (start : State) : Prop :=
  FiniteSafe (indexWidth wordFactor N q) heapWords rom program start ∧
    WordRefines (indexWidth wordFactor N q) rom program start ∧
    HaltingRuns rom.semantic program start (execute rom.semantic program start)
      (trace program ++ haltTrace)

def QueryClaims (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (t capWords heapWords : Nat)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (heap : Nat → Nat) : Prop :=
  let input := queryROM q full stage.val used
  let query := implementation.queryProgram full.length q t
  let result := execute input.semantic query (initial heap)
  totalQueryCost q query ≤ constant * queryWork q t ∧
    ExecutionClaims wordFactor full.length q heapWords input query (initial heap) ∧
    ReplyCorrect q (expectedReply q full hq stage used) result ∧
    (∀ address < tableWords full.length q t, result.heap address = heap address) ∧
    CapacityThroughout q capWords input query (initial heap)

structure Request (q N : Nat) where
  stage : Fin (N + 1)
  used : Finset (Fin q)

def pathExecute (implementation : Implementation) (q : Nat) (full : List (Finset (Fin q)))
    (t : Nat) : List (Request q full.length) → (Nat → Nat) → (Nat → Nat)
  | [], heap => heap
  | request :: later, heap =>
    let result := execute (queryROM q full request.stage.val request.used).semantic
      (implementation.queryProgram full.length q t) (initial heap)
    pathExecute implementation q full t later result.heap

def pathCost (implementation : Implementation) (q : Nat) (full : List (Finset (Fin q)))
    (t : Nat) (requests : List (Request q full.length)) : Nat :=
  (requests.map (fun _ => totalQueryCost q (implementation.queryProgram full.length q t))).sum

/-- Actual sequential workspaces are reused, rather than restarting every
query from the pre-query scratch contents.  This quantifies over arbitrary
request lists, and hence in particular over all realized causal histories. -/
def PathClaims (constant wordFactor : Nat) (implementation : Implementation)
    (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (t capWords heapWords : Nat) :
    List (Request q full.length) → (Nat → Nat) → Prop
  | [], _ => True
  | request :: later, heap =>
    QueryClaims constant wordFactor implementation q full hq t capWords heapWords
      request.stage request.used heap ∧
    let result := execute (queryROM q full request.stage.val request.used).semantic
      (implementation.queryProgram full.length q t) (initial heap)
    PathClaims constant wordFactor implementation q full hq t capWords heapWords later result.heap

/-- Complete positive-q *given-tree* A17 target.  The outer implementation
and constants precede all dimensions and all raw inputs. A06 is not assumed
completed by the existence of this interface. No theorem of this type is
asserted in this file. -/
def NatRAMImplementationClaims (constant wordFactor : Nat) (implementation : Implementation) : Prop :=
    ∀ (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q), LaminarSchedule full →
    let N := full.length
    let t := (prepareNormalization q full).indexed.nodes.size
    let rom := givenTreeROM q full
    let build := implementation.buildProgram N q t
    let capWords := implementation.capacityWords N q t
    let heapWords := capWords + implementation.indexWords N q t
    let built := execute rom.semantic build (initial (fun _ => 0))
    tableWords N q t ≤ capWords ∧
    capWords * CapacityBits.width q ≤ constant * work N q t * Nat.clog 2 (q + 2) ∧
    implementation.indexWords N q t ≤ constant * (N + q + t + 1) ∧
    totalBuildCost rom build heapWords ≤ constant * work N q t ∧
    ExecutionClaims wordFactor N q heapWords rom build (initial (fun _ => 0)) ∧
    PhysicalTableCorrect q full built.heap ∧
    CapacityThroughout q capWords rom build (initial (fun _ => 0)) ∧
    (∀ heap : Nat → Nat, PhysicalTableCorrect q full heap →
      CapacityPrefixBounded q capWords heap →
      (∀ address < heapWords, Fits (indexWidth wordFactor N q) (heap address)) →
      ∀ stage : Fin (N + 1), ∀ used : Finset (Fin q),
      QueryClaims constant wordFactor implementation q full hq t capWords heapWords stage used heap) ∧
    (let rolling := implementation.rollingProgram N q t
     let rollingCap := implementation.rollingCapacityWords N q t
     let rollingHeap := rollingCap + implementation.rollingIndexWords N q t
     ∀ used : Finset (Fin q),
     let input := queryROM q full 0 used
     let result := execute input.semantic rolling (initial (fun _ => 0))
     2 * (q + 2) * (t + 1) ≤ rollingCap ∧
     rollingCap * CapacityBits.width q ≤ constant * queryWork q t * Nat.clog 2 (q + 2) ∧
     implementation.rollingIndexWords N q t ≤ constant * (q + t + 1) ∧
     totalBuildCost input rolling rollingHeap ≤ constant * work N q t ∧
     ExecutionClaims wordFactor N q rollingHeap input rolling (initial (fun _ => 0)) ∧
     CapacityThroughout q rollingCap input rolling (initial (fun _ => 0)) ∧
     result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
     ∀ budget : Fin (q + 2), readEntry t budget.val result.heap =
       (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) ∧
    (∀ requests : List (Request q N), requests.length ≤ N →
      pathCost implementation q full t requests ≤ constant * N * queryWork q t ∧
      PathClaims constant wordFactor implementation q full hq t capWords heapWords requests built.heap ∧
      PhysicalTableCorrect q full (pathExecute implementation q full t requests built.heap))

def FullNatRAMClaims : Prop :=
  ∃ (constant wordFactor : Nat) (implementation : Implementation),
    0 < constant ∧ 0 < wordFactor ∧ NatRAMImplementationClaims constant wordFactor implementation

/-! The dense bit count is not inferred from small Nat values in a
uniform-width heap.  The following *additional pending obligation* supplies
a physical packed-word realization.  Standard word arithmetic/bit operations
are spelled out, and each has its own charged primitive.  There is no
"packed read", cell, row, or table instruction in this ISA. -/

inductive PackingPrimitive where
  | multiply | divide | bitAnd | bitOr | shiftLeft | shiftRight
  deriving DecidableEq

inductive PackingOp where
  | base (op : Op)
  | arithmetic (operation : PackingPrimitive) (target left right : Register)
  | jumpIfZero (condition target : Register)

def PackingPrimitive.word : PackingPrimitive → Nat
  | .multiply => 9 | .divide => 10 | .bitAnd => 11
  | .bitOr => 12 | .shiftLeft => 13 | .shiftRight => 14

def PackingPrimitive.fromWord : Nat → Option PackingPrimitive
  | 9 => some .multiply | 10 => some .divide | 11 => some .bitAnd
  | 12 => some .bitOr | 13 => some .shiftLeft | 14 => some .shiftRight | _ => none

def PackingOp.encode : PackingOp → Vector Nat 5
  | .base op => op.encodeWords
  | .arithmetic operation target left right =>
    ⟨#[operation.word, target.word, left.word, right.word, 0], rfl⟩
  | .jumpIfZero condition target => ⟨#[15, condition.word, target.word, 0, 0], rfl⟩

def PackingOp.decode (words : Vector Nat 5) : Option PackingOp :=
  if words[0] = 15 then do
    let condition ← Register.fromWord words[1]
    let target ← Register.fromWord words[2]
    pure (.jumpIfZero condition target)
  else if 9 ≤ words[0] then do
    let operation ← PackingPrimitive.fromWord words[0]
    let target ← Register.fromWord words[1]
    let left ← Register.fromWord words[2]
    let right ← Register.fromWord words[3]
    pure (.arithmetic operation target left right)
  else (Op.decodeWords words).map PackingOp.base

def PackingOp.events : PackingOp → List (Sum Event PackingPrimitive)
  | .base op => op.trace.map Sum.inl
  | .arithmetic operation _ _ _ =>
    (List.replicate 5 (.inl (.inl .instructionWordRead))) ++
      [.inl (.inl .decode), .inl (.inl .pcAdd), .inl (.inl .registerRead),
       .inl (.inl .registerRead), .inr operation, .inl (.inl .registerWrite)]
  | .jumpIfZero _ _ =>
    (List.replicate 5 (.inl (.inl .instructionWordRead))) ++
      [.inl (.inl .decode), .inl (.inl .registerRead), .inl (.inl .registerRead),
       .inl (.inl .conditionalSelect), .inl (.inl .pcAdd)]

def packingCode (program : List PackingOp) : List Nat :=
  program.flatMap (fun op => op.encode.toArray.toList) ++ haltWords.toArray.toList

def packingTrace (program : List PackingOp) : List (Sum Event PackingPrimitive) :=
  program.flatMap PackingOp.events ++ haltTrace.map Sum.inl

def packingArithmetic (operation : PackingPrimitive) (left right : BitVec bits) : BitVec bits :=
  BitVec.ofNat bits (match operation with
    | .multiply => left.toNat * right.toNat
    | .divide => left.toNat / right.toNat
    | .bitAnd => Nat.land left.toNat right.toNat
    | .bitOr => Nat.lor left.toNat right.toNat
    | .shiftLeft => Nat.shiftLeft left.toNat right.toNat
    | .shiftRight => Nat.shiftRight left.toNat right.toNat)

def packingExecuteOp (rom : PhysicalROM) : PackingOp → WordState bits → WordState bits
  | .base op, state => wordOp rom op state
  | .arithmetic operation target left right, state =>
    { state with
      register := Function.update state.register target
        (packingArithmetic operation (state.register left) (state.register right))
      pc := state.pc + BitVec.ofNat bits 5 }
  | .jumpIfZero condition target, state =>
    { state with pc := if (state.register condition).toNat = 0 then state.register target
        else state.pc + BitVec.ofNat bits 5 }

def packingStep (rom : PhysicalROM) (code : List (BitVec bits)) (state : WordState bits) : WordState bits :=
  if state.halted then state else
    let fetched : Vector Nat 5 := Vector.ofFn (fun position =>
      ((code.getD (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)
    match PackingOp.decode fetched with
    | none => { state with halted := true }
    | some op => packingExecuteOp rom op state

def packingRun (rom : PhysicalROM) (program : List PackingOp) : Nat → WordState bits → WordState bits
  | 0, state => state
  | count + 1, state =>
    packingRun rom program count (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state)

def packedCapacityWords (q capWords bits : Nat) : Nat :=
  (capWords * CapacityBits.width q + bits - 1) / bits

/-- Specification-only decoding of the actual physical words.  Runtime code
must realize this using the preceding arithmetic/bit ISA and is charged for
that work. A capacity may cross a word boundary. -/
def unpackHeap (q capWords bits : Nat) (heap : BitVec bits → BitVec bits) (address : Nat) : Nat :=
  if address < capWords then
    CapacityBits.decodeScalar (List.ofFn (fun position : Fin (CapacityBits.width q) =>
      let offset := address * CapacityBits.width q + position.val
      (heap (BitVec.ofNat bits (offset / bits))).getLsbD (offset % bits)))
  else (heap (BitVec.ofNat bits (packedCapacityWords q capWords bits + (address - capWords)))).toNat

def packingInitial (heap : BitVec bits → BitVec bits) : WordState bits :=
  ⟨fun _ => BitVec.ofNat bits 0, heap, BitVec.ofNat bits 0, false⟩

def packingAccessFits (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits) : PackingOp → Prop
  | .base op => AccessFits rom heapWords
      ⟨fun register => (state.register register).toNat,
       fun address => (state.heap (BitVec.ofNat bits address)).toNat, state.pc.toNat⟩ op
  | .arithmetic _ _ _ _ => True
  | .jumpIfZero _ _ => True

/-- These checks ensure that every listed instruction, and the terminal HALT,
is actually fetched; a malformed opcode/early HALT cannot satisfy the target. -/
def PackingRunCorrect (bits heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp)
    (heap : BitVec bits → BitVec bits) : Prop :=
  WordsFit bits (packingCode program) ∧
  (∀ region, WordsFit bits (rom.words region)) ∧
  Fits bits (rom.size + heapWords + (packingCode program).length) ∧
  (∀ count (hcount : count < program.length),
    let state := packingRun rom program count (packingInitial heap)
    state.halted = false ∧ state.pc.toNat = 5 * count ∧
      PackingOp.decode (Vector.ofFn (fun position =>
        ((((packingCode program).map (BitVec.ofNat bits)).getD
          (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)) = some program[count] ∧
      packingAccessFits rom heapWords state program[count]) ∧
  (let result := packingRun rom program program.length (packingInitial heap)
   result.halted = false ∧ result.pc.toNat = 5 * program.length ∧
   PackingOp.decode (Vector.ofFn (fun position =>
     ((((packingCode program).map (BitVec.ofNat bits)).getD
       (result.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)) = none ∧
   (packingRun rom program (program.length + 1) (packingInitial heap)).halted = true)

structure PackedPrograms where
  build : Nat → Nat → Nat → List PackingOp
  query : Nat → Nat → Nat → List PackingOp
  rolling : Nat → Nat → Nat → List PackingOp

def generatedCode (implementation : Implementation) (packed : PackedPrograms)
    (N q t : Nat) : List Nat :=
  [haltingWords (implementation.buildProgram N q t),
   haltingWords (implementation.queryProgram N q t),
   haltingWords (implementation.rollingProgram N q t),
   packingCode (packed.build N q t), packingCode (packed.query N q t),
   packingCode (packed.rolling N q t)].flatMap (fun code => code.length :: code)

/-- Actual event sequence for branching generator code. -/
def packingDynamicTrace (rom : PhysicalROM) (program : List PackingOp) :
    Nat → WordState bits → List (Sum Event PackingPrimitive)
  | 0, _ => []
  | count + 1, state =>
    if state.halted then [] else
      let fetched : Vector Nat 5 := Vector.ofFn (fun position =>
        ((((packingCode program).map (BitVec.ofNat bits)).getD
          (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)
      match PackingOp.decode fetched with
      | none => haltTrace.map Sum.inl
      | some op => op.events ++ packingDynamicTrace rom program count
          (packingExecuteOp rom op state)

/-- A single finite generator, independent even of N,q,t, must actually
emit all six complete programs.  The dimension restrictions below are the
already proved node-size bounds of the original input, not new eligibility
conditions. Generated code is not received through an oracle/ROM. -/
def UniformCodeGenerationClaims (constant wordFactor : Nat) (implementation : Implementation)
    (packed : PackedPrograms) : Prop :=
  ∃ generator : List PackingOp,
  ∀ (N q t : Nat), 0 < q → 0 < t → t ≤ N + q + 1 →
    let bits := indexWidth wordFactor N q
    let rom : PhysicalROM := ⟨[N, q, t], [], []⟩
    let start := packingInitial (fun _ => BitVec.ofNat bits 0)
    let target := generatedCode implementation packed N q t
    ∃ (steps heapWords : Nat),
    WordsFit bits (packingCode generator) ∧ WordsFit bits [N, q, t] ∧
    Fits bits (rom.size + heapWords + (packingCode generator).length) ∧
    target.length ≤ heapWords ∧
    (packingRun rom generator steps start).halted = true ∧
    (∀ position (hposition : position < target.length),
      ((packingRun rom generator steps start).heap (BitVec.ofNat bits position)).toNat = target[position]) ∧
    (∀ count < steps,
      let state := packingRun rom generator count start
      state.halted = false ∧ state.pc.toNat + 4 < (packingCode generator).length ∧
      let fetched : Vector Nat 5 := Vector.ofFn (fun position =>
        ((((packingCode generator).map (BitVec.ofNat bits)).getD
          (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)
      match PackingOp.decode fetched with
      | none => fetched = haltWords
      | some op => packingAccessFits rom heapWords state op) ∧
    rom.size + (packingCode generator).length + heapWords + 8 +
      (packingDynamicTrace rom generator steps start).length ≤ constant * work N q t

def PackedPhaseRefines (constant wordFactor N q t capWords indexWords : Nat)
    (rom : PhysicalROM) (logical : List Op) (packed : List PackingOp)
    (heap : BitVec (indexWidth wordFactor N q) → BitVec (indexWidth wordFactor N q)) : Prop :=
  let bits := indexWidth wordFactor N q
  let physicalWords := packedCapacityWords q capWords bits + indexWords
  let logicalHeap := unpackHeap q capWords bits heap
  let expected := execute rom.semantic logical (initial logicalHeap)
  let result := packingRun rom packed packed.length (packingInitial heap)
  PackingRunCorrect bits physicalWords rom packed heap ∧
  (∀ register, (result.register register).toNat = expected.register register) ∧
  (∀ address < capWords + indexWords, unpackHeap q capWords bits result.heap address = expected.heap address) ∧
  (∀ count ≤ packed.length, CapacityPrefixBounded q capWords
    (unpackHeap q capWords bits (packingRun rom packed count (packingInitial heap)).heap)) ∧
  (packingCode packed).length + (packingTrace packed).length + 8 ≤
    constant * ((haltingWords logical).length + (trace logical ++ haltTrace).length + 8) ∧
  physicalWords * bits ≤ capWords * CapacityBits.width q + (indexWords + 1) * bits ∧
  0 < t

/-- Uniform physical packing refinement of all three phases.  Query code
reuses the actual physical table heap.  It never receives an externally
decoded/repacked table between requests. The constants/programs precede all
raw input contents. This is an additional *unproved* part of A17. -/
def PackedImplementationClaims (constant wordFactor : Nat) (implementation : Implementation) : Prop :=
  ∃ packed : PackedPrograms,
  UniformCodeGenerationClaims constant wordFactor implementation packed ∧
  ∀ (q : Nat) (full : List (Finset (Fin q))) (_hq : 0 < q), LaminarSchedule full →
  let N := full.length
  let t := (prepareNormalization q full).indexed.nodes.size
  let rom := givenTreeROM q full
  let bits := indexWidth wordFactor N q
  let capWords := implementation.capacityWords N q t
  let indexWords := implementation.indexWords N q t
  PackedPhaseRefines constant wordFactor N q t capWords indexWords rom
    (implementation.buildProgram N q t) (packed.build N q t) (fun _ => BitVec.ofNat bits 0) ∧
  (∀ used : Finset (Fin q),
    PackedPhaseRefines constant wordFactor N q t (implementation.rollingCapacityWords N q t)
      (implementation.rollingIndexWords N q t) (queryROM q full 0 used)
      (implementation.rollingProgram N q t) (packed.rolling N q t) (fun _ => BitVec.ofNat bits 0)) ∧
  (∀ heap : BitVec bits → BitVec bits,
    let decoded := unpackHeap q capWords bits heap
    PhysicalTableCorrect q full decoded → CapacityPrefixBounded q capWords decoded →
    ∀ stage : Fin (N + 1), ∀ used : Finset (Fin q),
    PackedPhaseRefines constant wordFactor N q t capWords indexWords
      (queryROM q full stage.val used) (implementation.queryProgram N q t) (packed.query N q t) heap)

/-- The full A17 target includes both complete logical RAM execution and
the uniform physical packed-word realization. Stating it does not discharge
any implementation proof. A06 and the q=0 direct branch remain separate. -/
def FullGivenTreeClaims : Prop :=
  ∃ (constant wordFactor : Nat) (implementation : Implementation),
    0 < constant ∧ 0 < wordFactor ∧
    NatRAMImplementationClaims constant wordFactor implementation ∧
    PackedImplementationClaims constant wordFactor implementation

end PaperProofs.Structure.LaminarTree.AlgorithmClaims
