module

public import PaperProofs.Structure.RawTreePreprocessingClaims
public import PaperProofs.Structure.LaminarPlanExtraction
public import PaperProofs.Common.NativeHistoryReplay

/-!
Pending A19, frozen thm:laminar and laminar-proofs.tex:245--280.

The callback below fixes the actual indexed-table tie rule. It is not
identified with the generic subset evaluator's tool, path, or statistical
run. Its specification is independent game rank and the original causal
Plan/Play adversary, which may see every realized tool before continuing.

The runtime target is a fixed-code packed transducer. It receives raw
incidence and one initial used bitmap during preprocessing; subsequent
calls supply one public command only. The actual heap retains the table,
stage and used bitmap. Its query/update traces, finite words, loading,
initialization and HALT are charged. The semantic Plan is not stored.

This file states pending targets. It proves neither the implementation nor
any statistical risk/cost theorem. Native adapters expose only public
histories and retain the original handle/window/resource Step permissions.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.CompactControllerClaims

universe u

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims

variable {bits q : Nat}

/-- q=0 returns directly; this branch does not call prepareNormalization. -/
def callback (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) : IndexedQuery.Reply q :=
  if hq : 0 < q then expectedReply q full hq stage used else
    ⟨if stage.val < full.length then 1 else ⊤,
     if stage.val + 1 < full.length then 1 else ⊤, 0, none⟩

/-- This tree is the independent causal semantics of the callback. Runtime
code uses the compact table and bitmap; it does not construct this Plan. -/
def callbackPlan (q : Nat) (full : List (Finset (Fin q))) :
    (suffix : List (Finset (Fin q))) → Nat → Finset (Fin q) → Plan (Fin q) suffix
  | [], _, _ => .done
  | _ :: later, offset, used =>
    let good := callbackPlan q full later (offset + 1) used
    if h : offset < full.length + 1 then
      match (callback q full ⟨offset, h⟩ used).tool with
      | none => .decline good
      | some tool => .choose good tool (callbackPlan q full later (offset + 1) (insert tool used))
    else .decline good

def CallbackClaims : Prop :=
  ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full →
  (∀ (stage : Fin (full.length + 1)) (used : Finset (Fin q)),
    (callback q full stage used).rank = errorRank (full.drop stage.val) (Finset.univ \ used)) ∧
  (∀ (stage : Fin full.length) (used : Finset (Fin q)),
    let cursor : Fin (full.length + 1) := ⟨stage.val, by omega⟩
    let reply := callback q full cursor used
    reply.good = errorRank (full.drop (stage.val + 1)) (Finset.univ \ used) ∧
    reply.bad = badChildRank full[stage.val] (full.drop (stage.val + 1)) (Finset.univ \ used) ∧
    (reply.tool = none ↔ full[stage.val] ∩ (Finset.univ \ used) = ∅) ∧
    (∀ tool, reply.tool = some tool → tool ∈ full[stage.val] ∧ tool ∉ used ∧
      errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) = reply.bad)) ∧
  (∀ (offset : Fin (full.length + 1)) (used : Finset (Fin q)) (budget : Nat),
    SafePlan (callbackPlan q full (full.drop offset.val) offset.val used) (Finset.univ \ used) budget ↔
      Safe (full.drop offset.val) (Finset.univ \ used) budget)

inductive Command where
  | query | correct | error
  deriving DecidableEq

def Command.word : Command → Nat
  | .query => 0 | .correct => 1 | .error => 2

structure Configuration (q : Nat) where
  stage : Nat
  used : Finset (Fin q)
  failed : Bool

def Allowed (full : List (Finset (Fin q))) (configuration : Configuration q) : Command → Prop
  | .query => configuration.failed = false ∧ configuration.stage ≤ full.length
  | .correct | .error => configuration.failed = false ∧ configuration.stage < full.length

def nextConfiguration (q : Nat) (full : List (Finset (Fin q)))
    (configuration : Configuration q) : Command → Configuration q
  | .query => configuration
  | .correct => { configuration with stage := configuration.stage + 1 }
  | .error =>
    if h : configuration.stage < full.length + 1 then
      match (callback q full ⟨configuration.stage, h⟩ configuration.used).tool with
      | none => { configuration with failed := true }
      | some tool => { stage := configuration.stage + 1, used := insert tool configuration.used, failed := false }
    else { configuration with failed := true }

/-- One query followed by the current declaration, with the continuation
chosen after seeing the returned tool. All prefixes, including stopping at
failure, are allowed. No preselected subset of error stages is assumed. -/
inductive StageScript (q : Nat) (full : List (Finset (Fin q))) :
    Configuration q → List Command → Prop where
  | prefix (configuration) : StageScript q full configuration []
  | stage (configuration : Configuration q) (declaration : Command) (later : List Command)
      (isDeclaration : declaration = .correct ∨ declaration = .error)
      (allowed : Allowed full configuration declaration)
      (continuation : StageScript q full (nextConfiguration q full configuration declaration) later) :
      StageScript q full configuration (.query :: declaration :: later)

def treeSize (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  if q = 0 then 0 else (prepareNormalization q full).indexed.nodes.size

def liveWork (q t : Nat) : Nat := if q = 0 then 1 else queryWork q t

def preprocessingWork (N q t : Nat) : Nat :=
  if q = 0 then N + 1 else treeWork N q + work N q t

/-- Capacity region includes the table, the actual used bitmap and linear
scratch only. The zero-tool branch has no capacity/tree region. -/
def capacityWords (scratchFactor N q t : Nat) : Nat :=
  if q = 0 then 0 else tableWords N q t + q + scratchFactor * (t + 1)

/-- Fixed physical headers identify the stored layout without rescanning
all raw stages. These words are actual preprocessor outputs. -/
def physicalHeaderWords : Nat := 4

def dataHeap (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  fun address => heap (BitVec.ofNat bits (physicalHeaderWords + address.toNat))

def logicalHeap (q capWords : Nat) (heap : BitVec bits → BitVec bits) : Nat → Nat :=
  if q = 0 then fun address => (dataHeap heap (BitVec.ofNat bits address)).toNat
  else unpackHeap q capWords bits (dataHeap heap)

/-- Genuine compact cached tree/stage data materialized by preprocessing.
It is not supplied in controllerInput. Cardinalities and leaf/stage/tool
lookups must be computed from the original incidence. The live algorithm
may then reuse them without an uncharged search over N stage sets. -/
def staticMetadata (q : Nat) (full : List (Finset (Fin q))) : List Nat :=
  if hq : 0 < q then
    let cache := (prepareNormalization q full).indexed
    let nodes := List.finRange cache.nodes.size
    let children := nodes.flatMap (fun node => (cache.children.get node).toList.map Fin.val)
    let metadata := IndexedStaticMetadata.buildPositive q full hq
    [children.length] ++
      nodes.map (fun node => encodedNode cache (cache.parents.get node)) ++
      nodes.map (fun node => (cache.children.get node).size) ++ children ++
      nodes.map (fun node => cache.metadata.cardinalities.get node) ++
      nodes.map (fun node => bit (cache.metadata.isInternal.get node)) ++
      nodes.map (fun node => match (IndexedDescent.leafTools cache).get node with
        | none => 0 | some tool => tool.val + 1) ++
      (List.finRange full.length).map (fun stage => encodedNode cache (metadata.stageNodes.get stage)) ++
      (List.finRange q).map (fun tool => (metadata.toolNodes.get tool).val + 1)
  else []

def HeapRepresents (q : Nat) (full : List (Finset (Fin q))) (capWords : Nat)
    (configuration : Configuration q) (heap : BitVec bits → BitVec bits) : Prop :=
  let decoded := logicalHeap q capWords heap
  let t := treeSize q full
  (heap (BitVec.ofNat bits 0)).toNat = t ∧
  (heap (BitVec.ofNat bits 1)).toNat = capWords ∧
  (heap (BitVec.ofNat bits 2)).toNat = packedCapacityWords q capWords bits ∧
  (heap (BitVec.ofNat bits 3)).toNat = bits ∧
  decoded capWords = configuration.stage ∧
  decoded (capWords + 1) = bit configuration.failed ∧
  (∀ position (hposition : position < (staticMetadata q full).length),
    decoded (capWords + 2 + position) = (staticMetadata q full)[position]) ∧
  (∀ tool : Fin q, decoded (tableWords full.length q t + tool.val) = bit (decide (tool ∈ configuration.used))) ∧
  (0 < q → PhysicalTableCorrect q full decoded ∧ CapacityPrefixBounded q capWords decoded)

def controllerInput (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) : PhysicalROM :=
  let raw := rawIncidenceROM q full
  { raw with input := raw.input ++ (List.finRange q).map (fun tool => bit (decide (tool ∈ used))) }

/-- The only newly supplied live datum is the current public command.
Neither the current used set nor rank/tool answers are passed in again. -/
def callInput (q : Nat) (full : List (Finset (Fin q))) (command : Command) : PhysicalROM :=
  let raw := rawIncidenceROM q full
  { raw with input := raw.input ++ [command.word] }

def callCost (q : Nat) (full : List (Finset (Fin q))) (program : List PackingOp)
    (command : Command) (steps : Nat) (heap : BitVec bits → BitVec bits) : Nat :=
  1 + (packingCode program).length + 8 +
    (packingDynamicTrace (callInput q full command) program steps (packingInitial heap)).length

def replyState (q capWords : Nat) (state : WordState bits) : State :=
  ⟨fun register => (state.register register).toNat, logicalHeap q capWords state.heap, state.pc.toNat⟩

def CallClaims (constant : Nat) (q : Nat) (full : List (Finset (Fin q))) (capWords heapWords : Nat)
    (program : List PackingOp) (configuration : Configuration q) (command : Command)
    (steps : Nat) (heap : BitVec bits → BitVec bits) : Prop :=
  let input := callInput q full command
  let result := packingRun input program steps (packingInitial heap)
  DynamicRunCorrect heapWords input program steps heap ∧
  callCost q full program command steps heap ≤ constant * liveWork q (treeSize q full) ∧
  HeapRepresents q full capWords (nextConfiguration q full configuration command) result.heap ∧
  (∀ address < tableWords full.length q (treeSize q full), 0 < q →
    logicalHeap q capWords result.heap address = logicalHeap q capWords heap address) ∧
  (∀ count ≤ steps, 0 < q → CapacityPrefixBounded q capWords
    (logicalHeap q capWords (packingRun input program count (packingInitial heap)).heap)) ∧
  (∀ h : configuration.stage < full.length + 1,
    ReplyCorrect q (callback q full ⟨configuration.stage, h⟩ configuration.used)
      (replyState q capWords result))

def CommandsRunClaims (constant : Nat) (q : Nat) (full : List (Finset (Fin q)))
    (capWords heapWords : Nat) (program : List PackingOp) :
    Configuration q → List Command → List Nat → (BitVec bits → BitVec bits) → Prop
  | _, [], [], _ => True
  | configuration, command :: later, steps :: counts, heap =>
    Allowed full configuration command ∧
    CallClaims constant q full capWords heapWords program configuration command steps heap ∧
    CommandsRunClaims constant q full capWords heapWords program
      (nextConfiguration q full configuration command) later counts
      (packingRun (callInput q full command) program steps (packingInitial heap)).heap
  | _, _, _, _ => False

def commandsCost (q : Nat) (full : List (Finset (Fin q))) (program : List PackingOp) :
    List Command → List Nat → (BitVec bits → BitVec bits) → Nat
  | [], [], _ => 0
  | command :: later, steps :: counts, heap =>
    callCost q full program command steps heap + commandsCost q full program later counts
      (packingRun (callInput q full command) program steps (packingInitial heap)).heap
  | _, _, _ => 0

/-- One uniform fixed preprocessor and live program are selected before all
raw inputs. q=0 must run the direct implementation; q>0 must materialize the
same full-suffix table and keep it across every actual query/update call. -/
def MachineControllerClaims : Prop :=
  ∃ (constant wordFactor indexFactor scratchFactor : Nat) (preprocessor live : List PackingOp),
  0 < constant ∧ 0 < wordFactor ∧ 0 < indexFactor ∧ 0 < scratchFactor ∧
  ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full →
  ∀ initialUsed : Finset (Fin q),
  let N := full.length
  let t := treeSize q full
  let bits := indexWidth wordFactor N q
  let capWords := capacityWords scratchFactor N q t
  let indexWords := indexFactor * (N + q + t + 1)
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits + indexWords
  let input := controllerInput q full initialUsed
  let emptyHeap := fun _ => BitVec.ofNat bits 0
  let configuration : Configuration q := ⟨0, initialUsed, false⟩
  ∃ steps : Nat,
  let built := packingRun input preprocessor steps (packingInitial emptyHeap)
  DynamicRunCorrect heapWords input preprocessor steps emptyHeap ∧
  totalCost heapWords input preprocessor steps emptyHeap ≤ constant * preprocessingWork N q t ∧
  capWords * CapacityBits.width q ≤ constant * work N q t * Nat.clog 2 (q + 2) ∧
  HeapRepresents q full capWords configuration built.heap ∧
  (∀ configuration : Configuration q, ∀ heap : BitVec bits → BitVec bits,
    HeapRepresents q full capWords configuration heap →
    ∀ command : Command, Allowed full configuration command →
    ∃ steps : Nat, CallClaims constant q full capWords heapWords live configuration command steps heap) ∧
  (∀ commands : List Command, StageScript q full configuration commands →
    ∃ counts : List Nat,
    counts.length = commands.length ∧
    CommandsRunClaims constant q full capWords heapWords live configuration commands counts built.heap ∧
    commandsCost q full live commands counts built.heap ≤ 2 * constant * N * liveWork q t)

/-! Native integration deliberately keeps the original permissions. The
table tie may differ from the generic reference tie. No same-run equality,
statistical guarantee, cap change, new report, or synthetic commitment is
inserted in this adapter. -/

open PaperProofs.Common
open PaperProofs.Common.Native

def nativeExcluded (I : Instance) (initialAvailable : Finset I.Tool)
    (history : List (VisibleEvent I)) : Finset I.Tool :=
  (Finset.univ \ initialAvailable) ∪ historyUsed history

def nativeReply (I : Instance) (initialAvailable : Finset I.Tool)
    (history : List (VisibleEvent I)) : Option (IndexedQuery.Reply I.toolCount) :=
  if h : historyCursor history < I.compatibility.length + 1 then
    some (callback I.toolCount I.compatibility ⟨historyCursor history, h⟩ (nativeExcluded I initialAvailable history))
  else none

def NativeCallbackClaims : Prop :=
  ∀ (I : Instance), LaminarSchedule I.compatibility →
  ∀ (initialAvailable : Finset I.Tool) (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (Seed : Type u)
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (n : Nat) (state : Native.State I),
  Prefix input C mode accounting policy seed truth tapes n state →
  ∀ (stage : I.Stage), state.cursor = stage.val →
  ∃ reply, nativeReply I initialAvailable state.history = some reply ∧
    reply.rank = errorRank (I.compatibility.drop stage.val)
      (initialAvailable \ (state.ledger.commitments.map (·.tool)).toFinset) ∧
    reply.good = errorRank (I.compatibility.drop (stage.val + 1))
      (initialAvailable \ historyUsed state.history) ∧
    reply.bad = badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1))
      (initialAvailable \ historyUsed state.history) ∧
    (reply.tool = none ↔ I.eligible stage ∩ (initialAvailable \ historyUsed state.history) = ∅) ∧
    (∀ tool, reply.tool = some tool →
      tool ∈ initialAvailable ∧ tool ∈ I.eligible stage ∧ tool ∉ historyUsed state.history ∧
      errorRank (I.compatibility.drop (stage.val + 1))
        ((initialAvailable \ historyUsed state.history).erase tool) = reply.bad ∧
      ∀ (handle : MismatchHandle I), handle.stage = stage →
        state.halted = false → validHandle state handle →
        (∀ a ∈ state.ledger.commitments, a.handle.stage ≠ handle.stage) →
        allocationOpen C state handle.stage →
        withinResources C mode (record accounting state (.allocate handle tool) [.committed handle tool]
          (allocateLedger state handle tool) state.cursor false).ledger →
        Step input C mode accounting tapes state (.allocate handle tool)
          (record accounting state (.allocate handle tool) [.committed handle tool]
            (allocateLedger state handle tool) state.cursor false))

/-- Full A19 target with explicit A06/A17 obligations and original boundary,
causality, game-safety, physical-machine and Native-callback conclusions.
None of these pending implementation claims is inferred from compilation. -/
def FullClaims : Prop :=
  RawTreePreprocessingClaims.FullClaims ∧ AlgorithmClaims.FullGivenTreeClaims ∧
    CallbackClaims ∧ MachineControllerClaims ∧ NativeCallbackClaims.{u}

end PaperProofs.Structure.LaminarTree.CompactControllerClaims
