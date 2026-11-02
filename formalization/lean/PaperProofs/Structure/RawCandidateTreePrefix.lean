module

public import PaperProofs.Structure.RawCandidateMetadataPrefix
public import PaperProofs.Structure.RawCandidateParentRAM
public import PaperProofs.Structure.RawCandidateSerializedInputRun
public import PaperProofs.Structure.RawCandidateSerializedChildrenRAM
import Mathlib.Tactic.Linarith

/-! One actual raw-input program reaches the serialized-input handoff.
All cached tables and parent words are produced by its preceding phases;
the raw input is not augmented by any table or tree-answer premise. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateTreePrefix

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)

def parentStart : Nat := RawCandidateMetadataPrefix.orderingStart + 303

def inputStart : Nat := parentStart + 361

theorem parentStart_eq : parentStart = 845 := by
  simp only [parentStart, RawCandidateMetadataPrefix.orderingStart,
    RawCandidateMetadataPrefix.retentionStart, checker_length]

theorem inputStart_eq : inputStart = 1206 := by rw [inputStart, parentStart_eq]

def program (tail : List PackingOp) : List PackingOp :=
  RawCandidateMetadataPrefix.orderedProgram
    (RawCandidateParentRAM.programAt parentStart ++ RawCandidateSerializedInputRAM.programAt inputStart ++ tail)

def parentFront (tail : List PackingOp) : List PackingOp :=
  RawCandidateMetadataPrefix.orderingFront
    (RawCandidateParentRAM.programAt parentStart ++ RawCandidateSerializedInputRAM.programAt inputStart ++ tail) ++
      RawCandidateOrderingRAM.programAt RawCandidateMetadataPrefix.orderingStart

theorem parentFront_length (tail : List PackingOp) : (parentFront tail).length = parentStart := by
  simp only [parentFront, List.length_append, RawCandidateMetadataPrefix.orderingFront_length,
    RawCandidateOrderingRAM.programAt_length, parentStart]

theorem parentProgram_eq (tail : List PackingOp) :
    parentFront tail ++ RawCandidateParentRAM.programAt (parentFront tail).length ++
      (RawCandidateSerializedInputRAM.programAt inputStart ++ tail) = program tail := by
  rw [parentFront_length]
  have h := RawCandidateMetadataPrefix.orderedProgram_eq
    (RawCandidateParentRAM.programAt parentStart ++ RawCandidateSerializedInputRAM.programAt inputStart ++ tail)
  rw [RawCandidateMetadataPrefix.orderingFront_length] at h
  simpa only [parentFront, program, List.append_assoc] using h

def inputFront (tail : List PackingOp) : List PackingOp := parentFront tail ++ RawCandidateParentRAM.programAt parentStart

theorem inputFront_length (tail : List PackingOp) : (inputFront tail).length = inputStart := by
  simp only [inputFront, List.length_append, parentFront_length, RawCandidateParentRAM.programAt_length, inputStart]

theorem inputProgram_eq (tail : List PackingOp) :
    inputFront tail ++ RawCandidateSerializedInputRAM.programAt (inputFront tail).length ++ tail = program tail := by
  rw [inputFront_length]
  have h := parentProgram_eq tail
  rw [parentFront_length] at h
  simpa only [inputFront, List.append_assoc] using h

def serializedFront (tail : List PackingOp) : List PackingOp :=
  inputFront tail ++ RawCandidateSerializedInputRAM.programAt inputStart

theorem serializedFront_length (tail : List PackingOp) : (serializedFront tail).length = inputStart + 443 := by
  simp only [serializedFront, List.length_append, inputFront_length,
    RawCandidateSerializedInputRAM.programAt_length]

theorem serializedProgram_eq (tail : List PackingOp) : serializedFront tail ++ tail = program tail := by
  have h := inputProgram_eq tail
  rw [inputFront_length] at h
  exact h

theorem parent_slice (tail : List PackingOp) :
    parentStart + 361 ≤ (program tail).length ∧
      ∀ position < 361, (program tail).getD (parentStart + position) RawCandidateParentRAM.paddingOp =
        (RawCandidateParentRAM.programAt parentStart).getD position RawCandidateParentRAM.paddingOp := by
  have h := RawCandidateParentRAM.append_slice (parentFront tail)
    (RawCandidateSerializedInputRAM.programAt inputStart ++ tail)
  rw [parentProgram_eq, parentFront_length] at h
  exact h

theorem input_slice (tail : List PackingOp) :
    inputStart + 443 ≤ (program tail).length ∧
      ∀ position < 443, (program tail).getD (inputStart + position) RawCandidateSerializedInputRAM.paddingOp =
        (RawCandidateSerializedInputRAM.programAt inputStart).getD position RawCandidateSerializedInputRAM.paddingOp := by
  have h := RawCandidateSerializedInputRun.append_slice (inputFront tail) tail
  rw [inputProgram_eq, inputFront_length] at h
  exact h

def CachedParents (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ child : (prepareNormalization q full).indexed.NodeId,
    state.heap (RawCandidateParentRAM.parentSlot (workspaceBase full.length q) (full.length + q + 1) child.val) =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get child)

structure ParentEntry (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  input : RawCandidateSerializedInputRAM.InputSpec q full state
  parents : CachedParents q full state
  pc : state.pc = 5 * inputStart
  active : state.halted = false

theorem inputSpec_of_parent_tables (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before sortedState parentState : NatState)
    (sorted : RawCandidateOrderingRAM.Sorted q full (workspaceBase full.length q)
      RawCandidateMetadataPrefix.orderingStart before sortedState)
    (tables : RawCandidateParentRAM.InputTables q full (workspaceBase full.length q)
      (RawCandidateOrder.retainedCandidateIndices q full).length
      (RawCandidateParentRAM.observedOrder q full (workspaceBase full.length q) sortedState)
      (RawCandidateParentRAM.observedInverse q full (workspaceBase full.length q) sortedState) parentState) :
    RawCandidateSerializedInputRAM.InputSpec q full parentState := by
  have ht := RawCandidateParentRAM.prepared_nodes_eq_retained q full hq
  have hord (node : Nat) : RawCandidateSerializedInputRAM.ordAddress full.length q node =
      RawCandidateOrderingRAM.arraySlot (workspaceBase full.length q) (full.length + q + 1) 2 node := by
    unfold RawCandidateSerializedInputRAM.ordAddress RawCandidateOrderingRAM.arraySlot candidateCount
    omega
  constructor
  · have haddr : RawCandidateSerializedInputRAM.nodeCountAddress full.length q =
        RawCandidateParentRAM.nodeCountAddress (workspaceBase full.length q) (full.length + q + 1) := by
      unfold RawCandidateSerializedInputRAM.nodeCountAddress RawCandidateParentRAM.nodeCountAddress
        RawCandidateOrderingRAM.arraySlot candidateCount
      omega
    rw [haddr, tables.node_count]
    exact ht.symm
  · intro node hn
    have hretained : node < (RawCandidateOrder.retainedCandidateIndices q full).length := by omega
    rw [hord, tables.ordered node hretained]
    exact tables.order_valid node hretained
  · intro node hn
    have hretained : node < (RawCandidateOrder.retainedCandidateIndices q full).length := by omega
    rw [hord, tables.ordered node hretained]
    exact (RawCandidateParentRAM.observedOrder_support_of_sorted q full (workspaceBase full.length q)
      RawCandidateMetadataPrefix.orderingStart before sortedState sorted hq ⟨node, hn⟩).trans
        (RawCandidateSerializedInputRun.prepared_order_getD_eq_decode q full ⟨node, hn⟩).symm

def parentClockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  checkerSteps full.length q + 17 + RawCandidateRetentionRAM.totalSteps full.length q +
    RawCandidateOrderingRAM.totalSteps (full.length + q + 1) +
      512 * ((prepareNormalization q full).indexed.nodes.size + 1) * (full.length + q + 2) * (q + 1)

theorem parent_entry (tail : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ parentClockBound q full,
      ParentEntry q full (natRun (rawIncidenceROM q full) (program tail) clock natInitial) := by
  let base := workspaceBase full.length q
  let count := full.length + q + 1
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  obtain ⟨first, hfirst, sorted, _hzero⟩ := RawCandidateMetadataPrefix.sorted_entry
    (RawCandidateParentRAM.programAt parentStart ++ RawCandidateSerializedInputRAM.programAt inputStart ++ tail) q full hl
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  let sortedClock := first + RawCandidateOrderingRAM.totalSteps count
  let sortedState := natRun (rawIncidenceROM q full) (program tail) sortedClock natInitial
  have hs : RawCandidateOrderingRAM.Sorted q full base RawCandidateMetadataPrefix.orderingStart before sortedState := sorted
  let order := RawCandidateParentRAM.observedOrder q full base sortedState
  let inverse := RawCandidateParentRAM.observedInverse q full base sortedState
  let parentSteps := RawCandidateParentRAM.totalSteps full.length q nodes order
  have hlarge : 16 ≤ base := workspaceBase_ge full.length q
  have ht := RawCandidateParentRAM.InputTables.of_sorted q full base _ before sortedState hs hq
  have hpc : sortedState.pc = 5 * parentStart := hs.returned.pc
  have ha : sortedState.halted = false := hs.returned.active
  have hp := RawCandidateParentRAM.parents q full (program tail) parentStart (parent_slice tail).1 (parent_slice tail).2
    base nodes order inverse sortedState hlarge ht hpc ha
  have hprepared := RawCandidateParentRAM.parents_prepared q full hq (program tail) parentStart
    (parent_slice tail).1 (parent_slice tail).2 base RawCandidateMetadataPrefix.orderingStart before sortedState hlarge hs hpc ha
  dsimp only at hp hprepared
  have hrun : natRun (rawIncidenceROM q full) (program tail) parentSteps sortedState =
      natRun (rawIncidenceROM q full) (program tail) (sortedClock + parentSteps) natInitial :=
    (natRun_add _ _ _ _ _).symm
  have hcost := RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have hnodes : nodes = (prepareNormalization q full).indexed.nodes.size :=
    (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm
  rw [hnodes] at hcost
  refine ⟨sortedClock + parentSteps, ?_, ?_⟩
  · dsimp only [parentClockBound, sortedClock, parentSteps, count]
    rw [hnodes]
    omega
  · rw [← hrun]
    refine ⟨inputSpec_of_parent_tables q full hq before sortedState _ hs hp.1, hprepared, ?_, hp.2.2.2.2.2⟩
    exact hp.2.2.2.2.1

def prefixClockBound (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  parentClockBound q full + 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
    (prepareNormalization q full).indexed.nodes.size + 1)

structure SerializedEntry (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop where
  ready : RawCandidateSerializedReady.StageReady q full (5 * (inputStart + 443)) state
  written : ∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
    state.heap position = (serializeROM (givenTreeROM q full)).getD position 0
  parents : CachedParents q full state

theorem cachedParents_of_aboveFrame (q : Nat) (full : List (Finset (Fin q))) {before after : NatState}
    (hparents : CachedParents q full before)
    (hf : RawCandidateSerializedInputRAM.AboveFrame full.length q
      (RawCandidateSerializedInputLayout.prefixLength q full) before after) : CachedParents q full after := by
  have hb := workspaceBase_ge full.length q
  have hp : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q :=
    RawCandidateSerializedInputRAM.prefixLength_lt_base q full
  intro child
  have heq := hf (RawCandidateParentRAM.parentSlot (workspaceBase full.length q) (full.length + q + 1) child.val)
    (by unfold RawCandidateParentRAM.parentSlot RawCandidateOrderingRAM.arraySlot; omega)
    (by unfold RawCandidateParentRAM.parentSlot RawCandidateOrderingRAM.arraySlot; omega)
    (by unfold RawCandidateParentRAM.parentSlot RawCandidateOrderingRAM.arraySlot; omega)
    (by unfold RawCandidateParentRAM.parentSlot RawCandidateOrderingRAM.arraySlot; omega)
  exact heq.trans (hparents child)

theorem serialized_entry (tail : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ prefixClockBound q full,
      SerializedEntry q full (natRun (rawIncidenceROM q full) (program tail) clock natInitial) := by
  obtain ⟨first, hfirst, entry⟩ := parent_entry tail q full hq hl
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  obtain ⟨steps, hsteps, ready, written, hframe⟩ :=
    RawCandidateSerializedInputRun.materialize_serialized_prefix q full (program tail) inputStart
      (input_slice tail).1 (input_slice tail).2 before entry.input entry.pc entry.active hq hl
  have hparents := cachedParents_of_aboveFrame q full entry.parents hframe
  have hrun : natRun (rawIncidenceROM q full) (program tail) steps before =
      natRun (rawIncidenceROM q full) (program tail) (first + steps) natInitial :=
    (natRun_add _ _ _ _ _).symm
  refine ⟨first + steps, by unfold prefixClockBound; omega, ?_⟩
  rw [← hrun]
  exact ⟨ready, written, hparents⟩

theorem SerializedEntry.children_input {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : SerializedEntry q full state) : RawCandidateSerializedChildrenRAM.InputSpec q full state := by
  refine ⟨entry.ready.headers, ?_⟩
  intro child hc
  have hp := entry.parents ⟨child, hc⟩
  have haddr : RawCandidateSerializedChildrenRAM.parentAddress full.length q child =
      RawCandidateParentRAM.parentSlot (workspaceBase full.length q) (full.length + q + 1) child := by
    unfold RawCandidateSerializedChildrenRAM.parentAddress RawCandidateParentRAM.parentSlot
      RawCandidateOrderingRAM.arraySlot candidateCount
    omega
  rw [haddr]
  exact hp.trans (RawCandidateChildrenLayout.givenTreeROM_parentWords q full child hc).symm

theorem serialized_exit_pc {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (entry : SerializedEntry q full state) : state.pc = 5 * 1649 := by
  simpa only [inputStart_eq] using entry.ready.pc

end PaperProofs.Structure.LaminarTree.RawCandidateTreePrefix
