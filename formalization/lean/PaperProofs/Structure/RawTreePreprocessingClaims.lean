module

public import PaperProofs.Structure.AlgorithmClaims

/-!
Pending A06, frozen laminar-proofs.tex:235--243.

The raw input contains exactly the explicit N-by-q incidence bits and its
dimensions. A single finite program, chosen before N,q and every incidence
input, must check laminarity and construct the actual given-tree ROM used
by A17. In particular prepareNormalization is used only in the output
specification: none of its nodes/parents/metadata are supplied to the
machine. Set equality, containment, intersection/cardinality, deduplication,
argmin parent search and sorting are not machine primitives.

This is a statement interface, not a proof that such a program exists.
The positive-q construction and the zero-tool direct branch are separate,
as in the paper. Repeated stages and unused tools stay in the quantifiers.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingClaims

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {bits : Nat}

/-- No supplied tree, table, stage-node map, cardinality, parent pointer,
rank, strategy, or trace is part of this physical input. -/
def rawIncidenceROM (q : Nat) (full : List (Finset (Fin q))) : PhysicalROM :=
  ⟨[full.length, q] ++ incidence full, [], []⟩

def treeWork (N q : Nat) : Nat := (N + q + 1) ^ 2 * q

def fetch (program : List PackingOp) (state : WordState bits) : Vector Nat 5 :=
  Vector.ofFn (fun position =>
    ((((packingCode program).map (BitVec.ofNat bits)).getD
      (state.pc.toNat + position.val) (BitVec.ofNat bits 0))).toNat)

/-- Branching execution uses the existing physical fixed-word ISA and its
actual fetch/decode/access events. A malformed opcode, early stopped state,
out-of-range access or uncharged terminal instruction cannot satisfy this
predicate. No host evaluator's time is asserted here. -/
def DynamicRunCorrect (heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp)
    (steps : Nat) (heap : BitVec bits → BitVec bits) : Prop :=
  WordsFit bits (packingCode program) ∧
  (∀ region, WordsFit bits (rom.words region)) ∧
  Fits bits (rom.size + heapWords + (packingCode program).length) ∧
  (packingRun rom program steps (packingInitial heap)).halted = true ∧
  (∀ count < steps,
    let state := packingRun rom program count (packingInitial heap)
    state.halted = false ∧ state.pc.toNat + 4 < (packingCode program).length ∧
    match PackingOp.decode (fetch program state) with
    | none => fetch program state = haltWords
    | some op => packingAccessFits rom heapWords state op)

def totalCost (heapWords : Nat) (rom : PhysicalROM) (program : List PackingOp)
    (steps : Nat) (heap : BitVec bits → BitVec bits) : Nat :=
  rom.size + (packingCode program).length + heapWords + 8 +
    (packingDynamicTrace rom program steps (packingInitial heap)).length

/-- Output is actual serialized data, including all three region lengths.
The subsequent A17 loader can copy exactly these words; it is not allowed
to call prepareNormalization to manufacture a correct ROM for free. -/
def serializeROM (rom : PhysicalROM) : List Nat :=
  [rom.input.length, rom.internal.length, rom.children.length] ++
    rom.input ++ rom.internal ++ rom.children

def heapWordsAt (heap : BitVec bits → BitVec bits) (offset length : Nat) : List Nat :=
  (List.range length).map (fun position => (heap (BitVec.ofNat bits (offset + position))).toNat)

def readSerializedROM (heap : BitVec bits → BitVec bits) : PhysicalROM :=
  let inputLength := (heap (BitVec.ofNat bits 0)).toNat
  let internalLength := (heap (BitVec.ofNat bits 1)).toNat
  let childrenLength := (heap (BitVec.ofNat bits 2)).toNat
  ⟨heapWordsAt heap 3 inputLength,
   heapWordsAt heap (3 + inputLength) internalLength,
   heapWordsAt heap (3 + inputLength + internalLength) childrenLength⟩

def TreeOutputCorrect (q : Nat) (full : List (Finset (Fin q))) (heapWords : Nat)
    (result : WordState bits) : Prop :=
  let target := givenTreeROM q full
  let serialized := serializeROM target
  let t := (prepareNormalization q full).indexed.nodes.size
  (result.register .old).toNat = t ∧
  (result.register .fresh).toNat = serialized.length ∧
  serialized.length ≤ heapWords ∧
  (∀ position (hposition : position < serialized.length),
    (result.heap (BitVec.ofNat bits position)).toNat = serialized[position]) ∧
  readSerializedROM result.heap = target ∧
  t ≤ full.length + q + 1

/-- Entire positive-q explicit-input A06 claim. Correct rejection is
required for every nonlaminar input too, within the same work bound. The
single code and constants precede all dimensions and incidence contents.
The cost includes code/ROM loading, writable-memory initialization, actual
primitive operations, output materialization and encoded HALT. -/
def FullClaims : Prop :=
  ∃ (constant wordFactor : Nat) (program : List PackingOp),
    0 < constant ∧ 0 < wordFactor ∧
    ∀ (q : Nat) (full : List (Finset (Fin q))), 0 < q →
    let N := full.length
    let bits := indexWidth wordFactor N q
    let rom := rawIncidenceROM q full
    let heap := fun _ => BitVec.ofNat bits 0
    ∃ (steps heapWords : Nat),
    DynamicRunCorrect heapWords rom program steps heap ∧
    totalCost heapWords rom program steps heap ≤ constant * treeWork N q ∧
    (let result := packingRun rom program steps (packingInitial heap)
     (result.register .value).toNat ≤ 1 ∧
     ((result.register .value).toNat = 1 ↔ LaminarSchedule full) ∧
     (LaminarSchedule full → TreeOutputCorrect q full heapWords result))

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingClaims
