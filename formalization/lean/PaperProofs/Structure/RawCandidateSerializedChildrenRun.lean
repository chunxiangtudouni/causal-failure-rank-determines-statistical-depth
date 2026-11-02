module

public import PaperProofs.Structure.RawCandidateSerializedChildrenRAM
public import PaperProofs.Structure.RawCandidateChildrenPrefix
import Mathlib.Tactic.Linarith

/-! Actual runtime loops for the fixed child serializer.  The finite sums
below count proved runs of its runtime loops; they do not generate code. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenRun

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedChildrenRAM
  RawCandidateChildrenLayout RawCandidateChildrenPrefix
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge)
open RawCandidateSerializedInputRAM (boundedTest boundedTest_values)

def beforeList (q : Nat) (full : List (Finset (Fin q))) (node : Nat) : List Nat :=
  flatPrefix (size q full) (parentWords q full) node

def rowList (q : Nat) (full : List (Finset (Fin q))) (node child : Nat) : List Nat :=
  childPrefix (size q full) (parentWords q full) node child

def scanList (q : Nat) (full : List (Finset (Fin q))) (node child : Nat) : List Nat :=
  beforeList q full node ++ rowList q full node child

def Written (base : Nat) (words : List Nat) (state : NatState) : Prop :=
  ∀ position < words.length, state.heap (base + position) = words.getD position 0

theorem Written.nil (base : Nat) (state : NatState) : Written base [] state := by
  intro position hp
  simp only [List.length_nil] at hp
  omega

theorem Written.of_heap_eq {base : Nat} {words : List Nat} {before after : NatState}
    (h : Written base words before) (hh : after.heap = before.heap) : Written base words after := by
  intro position hp
  rw [hh]
  exact h position hp

theorem Written.snoc {base word : Nat} {words : List Nat} {before after : NatState}
    (hw : Written base words before)
    (hold : ∀ position < words.length, after.heap (base + position) = before.heap (base + position))
    (hnew : after.heap (base + words.length) = word) : Written base (words ++ [word]) after := by
  intro position hp
  simp only [List.length_append, List.length_cons, List.length_nil] at hp
  by_cases hi : position < words.length
  · rw [List.getD_append _ _ _ _ hi, hold position hi]
    exact hw position hi
  · have heq : position = words.length := by omega
    rw [heq, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    exact hnew

theorem scanList_zero (q : Nat) (full : List (Finset (Fin q))) (node : Nat) :
    scanList q full node 0 = beforeList q full node := by
  simp only [scanList, rowList, childPrefix_zero, List.append_nil]

theorem scanList_succ (q : Nat) (full : List (Finset (Fin q))) (node child : Nat) :
    scanList q full node (child + 1) = if parentWords q full child = node + 1 then
      scanList q full node child ++ [child] else scanList q full node child := by
  simp only [scanList, rowList, childPrefix_succ]
  split <;> simp only [List.append_assoc]

theorem scanList_full (q : Nat) (full : List (Finset (Fin q))) (node : Nat) :
    scanList q full node (size q full) = beforeList q full (node + 1) := by
  simp only [scanList, rowList, beforeList, childPrefix_full, flatPrefix_succ]

theorem beforeList_full (q : Nat) (full : List (Finset (Fin q))) :
    beforeList q full (size q full) = (givenTreeROM q full).children :=
  flatChildren_givenTreeROM q full

theorem scanList_length_le (q : Nat) (full : List (Finset (Fin q))) (node child : Nat)
    (hn : node < size q full) (hc : child ≤ size q full) :
    (scanList q full node child).length ≤ (givenTreeROM q full).children.length := by
  have h := partial_span_le_total (size q full) (parentWords q full) node child hn hc
  rw [show flatChildren (size q full) (parentWords q full) = (givenTreeROM q full).children from
    flatChildren_givenTreeROM q full] at h
  simpa only [scanList, beforeList, rowList, List.length_append] using h

theorem matched_position_lt (q : Nat) (full : List (Finset (Fin q))) (node child : Nat)
    (hn : node < size q full) (hc : child < size q full) (heq : parentWords q full child = node + 1) :
    childrenStart q full + (scanList q full node child).length < endAddress q full := by
  have h := matched_write_lt_total (size q full) (parentWords q full) node child hn hc heq
  rw [show flatChildren (size q full) (parentWords q full) = (givenTreeROM q full).children from
    flatChildren_givenTreeROM q full] at h
  simp only [scanList, beforeList, rowList, List.length_append, endAddress]
  omega

structure OuterReady (q : Nat) (full : List (Finset (Fin q))) (node pointer : Nat) (state : NatState) : Prop where
  input : RawCandidateSerializedChildrenRAM.InputSpec q full state
  node_cell : state.heap (workspaceBase full.length q + 1) = node
  flat_cell : state.heap (flatAddress full.length q) = (beforeList q full node).length
  parents : ∀ parent < node, state.heap (internalStart q full + parent) = parentWords q full parent
  degrees : ∀ parent < node, state.heap (internalStart q full + size q full + parent) =
    (rowList q full parent (size q full)).length
  children : Written (childrenStart q full) (beforeList q full node) state
  pc : state.pc = pointer
  active : state.halted = false

structure InnerReady (q : Nat) (full : List (Finset (Fin q))) (node child pointer : Nat) (state : NatState) : Prop where
  cursor : CursorReady q full node child pointer state
  degree_cell : state.heap (workspaceBase full.length q + 3) = (rowList q full node child).length
  flat_cell : state.heap (flatAddress full.length q) = (scanList q full node child).length
  parents : ∀ parent < node + 1, state.heap (internalStart q full + parent) = parentWords q full parent
  degrees : ∀ parent < node, state.heap (internalStart q full + size q full + parent) =
    (rowList q full parent (size q full)).length
  children : Written (childrenStart q full) (scanList q full node child) state

theorem bit_heap_frame (q : Nat) (full : List (Finset (Fin q))) (node child : Nat)
    {before after : NatState}
    (hh : after.heap = bitHeap q full node child before)
    (hwrite : parentWords q full child = node + 1 →
      internalStart q full ≤ childrenStart q full + before.heap (flatAddress full.length q) ∧
        childrenStart q full + before.heap (flatAddress full.length q) < endAddress q full) :
    Frame q full before after := by
  intro address hp
  rcases hp with ⟨h1, h2, h3, hf, hp⟩
  rw [hh]
  by_cases heq : parentWords q full child = node + 1
  · have hspan := hwrite heq
    have hn : address ≠ childrenStart q full + before.heap (flatAddress full.length q) := by
      rcases hp with hp | hp <;> omega
    simp only [bitHeap, ite_eq_left heq]
    simp [h2, hf, h3, hn]
  · simp only [bitHeap, ite_eq_right heq]
    exact Function.update_of_ne h2 _ _

theorem bit_heap_ready (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (node child pointer nextPointer : Nat) {before after : NatState}
    (ready : InnerReady q full node child pointer before)
    (hn : node < size q full) (hc : child < size q full)
    (hh : after.heap = bitHeap q full node child before)
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    InnerReady q full node (child + 1) nextPointer after ∧ Frame q full before after := by
  have hb := workspaceBase_ge full.length q
  have hflat : workspaceBase full.length q + 5 ≤ flatAddress full.length q := by unfold flatAddress; omega
  have hend := endAddress_lt_base q full hq hl
  have hstart : internalStart q full + 2 * size q full ≤ endAddress q full := by
    unfold endAddress childrenStart
    omega
  have hdst (heq : parentWords q full child = node + 1) :
      childrenStart q full + before.heap (flatAddress full.length q) < endAddress q full := by
    rw [ready.flat_cell]
    exact matched_position_lt q full node child hn hc heq
  have hf := bit_heap_frame q full node child hh (fun heq => ⟨by unfold childrenStart; omega, hdst heq⟩)
  have hinput := RawCandidateSerializedChildrenRAM.InputSpec.of_frame hq hl ready.cursor.input hf
  have hbelow : ∀ address < childrenStart q full, after.heap address = before.heap address := by
    intro address haddress
    have hdb : address < workspaceBase full.length q := by unfold childrenStart at haddress; omega
    rw [hh]
    by_cases heq : parentWords q full child = node + 1
    · simp (disch := omega) [bitHeap, heq]
    · simp (disch := omega) [bitHeap, heq]
  refine ⟨?_, hf⟩
  constructor
  · refine ⟨hinput, ?_, ?_, hp, ha⟩
    · rw [hh]
      by_cases heq : parentWords q full child = node + 1
      · have hd := hdst heq
        simpa (disch := omega) [bitHeap, heq] using ready.cursor.node_cell
      · simpa [bitHeap, heq] using ready.cursor.node_cell
    · rw [hh]
      simp [bitHeap]
  · rw [hh, rowList, childPrefix_length_succ]
    by_cases heq : parentWords q full child = node + 1
    · have hd := hdst heq
      simpa (disch := omega) [bitHeap, heq, rowList] using ready.degree_cell
    · simpa (disch := omega) [bitHeap, heq, rowList] using ready.degree_cell
  · rw [hh, scanList_succ]
    by_cases heq : parentWords q full child = node + 1
    · have hd := hdst heq
      simpa (disch := omega) [bitHeap, heq] using ready.flat_cell
    · simpa (disch := omega) [bitHeap, heq] using ready.flat_cell
  · intro parent hparent
    exact (hbelow _ (by unfold childrenStart; omega)).trans (ready.parents parent hparent)
  · intro parent hparent
    exact (hbelow _ (by unfold childrenStart; omega)).trans (ready.degrees parent hparent)
  · rw [scanList_succ]
    by_cases heq : parentWords q full child = node + 1
    · rw [ite_eq_left heq]
      apply Written.snoc ready.children
      · intro position hposition
        have hd := hdst heq
        have hpos : childrenStart q full + position < workspaceBase full.length q := by rw [ready.flat_cell] at hd; omega
        rw [hh]
        simp (disch := omega) [bitHeap, heq, ready.flat_cell]
      · have hd := hdst heq
        rw [ready.flat_cell] at hd
        rw [hh]
        simp (disch := omega) [bitHeap, heq, ready.flat_cell]
    · rw [ite_eq_right heq]
      intro position hposition
      have hspan := scanList_length_le q full node child hn hc.le
      have hpos : childrenStart q full + position < workspaceBase full.length q := by unfold endAddress at hend; omega
      rw [hh]
      simpa (disch := omega) [bitHeap, heq] using ready.children position hposition

theorem beforeList_length_le (q : Nat) (full : List (Finset (Fin q))) (node : Nat)
    (hn : node ≤ size q full) :
    (beforeList q full node).length ≤ (givenTreeROM q full).children.length := by
  have h := flatPrefix_length_mono (size q full) (parentWords q full) node (size q full) hn
  change (beforeList q full node).length ≤ (beforeList q full (size q full)).length at h
  rwa [beforeList_full] at h

theorem init_heap_ready (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (pointer : Nat) {before after : NatState}
    (hspec : RawCandidateSerializedChildrenRAM.InputSpec q full before)
    (hh : after.heap = Function.update (Function.update before.heap (workspaceBase full.length q + 1) 0)
      (flatAddress full.length q) 0)
    (hp : after.pc = pointer) (ha : after.halted = false) :
    OuterReady q full 0 pointer after ∧ Frame q full before after := by
  have hf : Frame q full before after := by
    intro address haddress
    rw [hh]
    simp [haddress.1, haddress.2.2.2.1]
  refine ⟨?_, hf⟩
  constructor
  · exact RawCandidateSerializedChildrenRAM.InputSpec.of_frame hq hl hspec hf
  · rw [hh]
    simp (disch := omega) [flatAddress]
  · rw [hh]
    simp only [Function.update_self, beforeList, flatPrefix_zero, List.length_nil]
  · intro parent hparent
    omega
  · intro parent hparent
    omega
  · simpa only [beforeList, flatPrefix_zero] using Written.nil (childrenStart q full) after
  · exact hp
  · exact ha

theorem row_init_heap_ready (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (node pointer nextPointer : Nat) {before after : NatState}
    (ready : OuterReady q full node pointer before) (hn : node < size q full)
    (hh : after.heap = Function.update (Function.update
      (Function.update before.heap (internalStart q full + node) (parentWords q full node))
        (workspaceBase full.length q + 3) 0) (workspaceBase full.length q + 2) 0)
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    InnerReady q full node 0 nextPointer after ∧ Frame q full before after := by
  have hb := workspaceBase_ge full.length q
  have hend := endAddress_lt_base q full hq hl
  have hspan : internalStart q full + 2 * size q full ≤ endAddress q full := by
    unfold endAddress childrenStart
    omega
  have hd : internalStart q full + node < workspaceBase full.length q := by omega
  have hf : Frame q full before after := by
    intro address haddress
    have hne : address ≠ internalStart q full + node := by
      rcases haddress.2.2.2.2 with hleft | hright <;> omega
    rw [hh]
    simp [haddress.2.1, haddress.2.2.1, hne]
  refine ⟨?_, hf⟩
  constructor
  · refine ⟨RawCandidateSerializedChildrenRAM.InputSpec.of_frame hq hl ready.input hf, ?_, ?_, hp, ha⟩
    · rw [hh]
      simpa (disch := omega) using ready.node_cell
    · rw [hh]
      simp
  · rw [hh]
    simp only [Function.update_of_ne (by omega : workspaceBase full.length q + 3 ≠ workspaceBase full.length q + 2),
      Function.update_self, rowList, childPrefix_zero, List.length_nil]
  · rw [hh, scanList_zero]
    simpa (disch := omega) [flatAddress] using ready.flat_cell
  · intro parent hparent
    rw [hh]
    by_cases heq : parent = node
    · subst parent
      simp (disch := omega)
    · have hpast : parent < node := by omega
      simpa (disch := omega) [show internalStart q full + parent ≠ internalStart q full + node by omega] using
        ready.parents parent hpast
  · intro parent hparent
    rw [hh]
    simpa (disch := omega) [show internalStart q full + size q full + parent ≠ internalStart q full + node by omega] using
      ready.degrees parent hparent
  · rw [scanList_zero]
    intro position hposition
    have hlen := beforeList_length_le q full node hn.le
    have hpos : childrenStart q full + position < workspaceBase full.length q := by unfold endAddress at hend; omega
    rw [hh, Function.update_of_ne (by omega : childrenStart q full + position ≠ workspaceBase full.length q + 2),
      Function.update_of_ne (by omega : childrenStart q full + position ≠ workspaceBase full.length q + 3),
      Function.update_of_ne (by unfold childrenStart; omega : childrenStart q full + position ≠ internalStart q full + node)]
    exact ready.children position hposition

theorem row_finish_heap_ready (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (node pointer nextPointer : Nat) {before after : NatState}
    (ready : InnerReady q full node (size q full) pointer before) (hn : node < size q full)
    (hh : after.heap = Function.update
      (Function.update before.heap (internalStart q full + size q full + node)
        ((rowList q full node (size q full)).length))
      (workspaceBase full.length q + 1) (node + 1))
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    OuterReady q full (node + 1) nextPointer after ∧ Frame q full before after := by
  have hb := workspaceBase_ge full.length q
  have hend := endAddress_lt_base q full hq hl
  have hspan : internalStart q full + 2 * size q full ≤ endAddress q full := by
    unfold endAddress childrenStart
    omega
  have hd : internalStart q full + size q full + node < workspaceBase full.length q := by omega
  have hf : Frame q full before after := by
    intro address haddress
    have hne : address ≠ internalStart q full + size q full + node := by
      rcases haddress.2.2.2.2 with hleft | hright <;> omega
    rw [hh]
    simp [haddress.1, hne]
  refine ⟨?_, hf⟩
  constructor
  · exact RawCandidateSerializedChildrenRAM.InputSpec.of_frame hq hl ready.cursor.input hf
  · rw [hh]
    simp
  · rw [hh, ← scanList_full]
    simpa (disch := omega) [flatAddress] using ready.flat_cell
  · intro parent hparent
    rw [hh]
    simpa (disch := omega) [show internalStart q full + parent ≠ internalStart q full + size q full + node by omega] using
      ready.parents parent hparent
  · intro parent hparent
    rw [hh]
    by_cases heq : parent = node
    · subst parent
      simp (disch := omega)
    · have hpast : parent < node := by omega
      simpa (disch := omega) [show internalStart q full + size q full + parent ≠ internalStart q full + size q full + node by omega] using
        ready.degrees parent hpast
  · rw [← scanList_full]
    intro position hposition
    have hlen := scanList_length_le q full node (size q full) hn le_rfl
    have hpos : childrenStart q full + position < workspaceBase full.length q := by unfold endAddress at hend; omega
    rw [hh, Function.update_of_ne (by omega : childrenStart q full + position ≠ workspaceBase full.length q + 1),
      Function.update_of_ne (by unfold childrenStart; omega : childrenStart q full + position ≠ internalStart q full + size q full + node)]
    exact ready.children position hposition
  · exact hp
  · exact ha

theorem input_of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : RawCandidateSerializedChildrenRAM.InputSpec q full before) (hh : after.heap = before.heap) :
    RawCandidateSerializedChildrenRAM.InputSpec q full after := by
  constructor
  · exact RawCandidateSerializedReady.HeaderSpec.of_heap_eq h.headers hh
  · intro child hc
    rw [hh]
    exact h.parents child hc

theorem frame_of_heap_eq (q : Nat) (full : List (Finset (Fin q))) {before after : NatState}
    (hh : after.heap = before.heap) : Frame q full before after := fun address _ => congrFun hh address

theorem OuterReady.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {node pointer nextPointer : Nat}
    {before after : NatState} (h : OuterReady q full node pointer before)
    (hh : after.heap = before.heap) (hp : after.pc = nextPointer) (ha : after.halted = false) :
    OuterReady q full node nextPointer after := by
  refine ⟨input_of_heap_eq h.input hh, (congrFun hh _).trans h.node_cell,
    (congrFun hh _).trans h.flat_cell, ?_, ?_, Written.of_heap_eq h.children hh, hp, ha⟩
  · intro parent hparent
    exact (congrFun hh _).trans (h.parents parent hparent)
  · intro parent hparent
    exact (congrFun hh _).trans (h.degrees parent hparent)

theorem InnerReady.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {node child pointer nextPointer : Nat}
    {before after : NatState} (h : InnerReady q full node child pointer before)
    (hh : after.heap = before.heap) (hp : after.pc = nextPointer) (ha : after.halted = false) :
    InnerReady q full node child nextPointer after := by
  refine ⟨⟨input_of_heap_eq h.cursor.input hh, (congrFun hh _).trans h.cursor.node_cell,
    (congrFun hh _).trans h.cursor.child_cell, hp, ha⟩,
    (congrFun hh _).trans h.degree_cell, (congrFun hh _).trans h.flat_cell,
    ?_, ?_, Written.of_heap_eq h.children hh⟩
  · intro parent hparent
    exact (congrFun hh _).trans (h.parents parent hparent)
  · intro parent hparent
    exact (congrFun hh _).trans (h.degrees parent hparent)

def childSteps (q : Nat) (full : List (Finset (Fin q))) (node count : Nat) : Nat :=
  ∑ child ∈ Finset.range count, bitSteps (parentWords q full) node child

theorem childSteps_succ (q : Nat) (full : List (Finset (Fin q))) (node count : Nat) :
    childSteps q full node (count + 1) = childSteps q full node count + bitSteps (parentWords q full) node count :=
  Finset.sum_range_succ _ _

def rowSteps (q : Nat) (full : List (Finset (Fin q))) (node : Nat) : Nat :=
  186 + childSteps q full node (size q full)

def outerSteps (q : Nat) (full : List (Finset (Fin q))) (count : Nat) : Nat :=
  ∑ node ∈ Finset.range count, rowSteps q full node

theorem outerSteps_succ (q : Nat) (full : List (Finset (Fin q))) (count : Nat) :
    outerSteps q full (count + 1) = outerSteps q full count + rowSteps q full count :=
  Finset.sum_range_succ _ _

def totalSteps (q : Nat) (full : List (Finset (Fin q))) : Nat := 35 + outerSteps q full (size q full) + 20

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
  (containing : List PackingOp) (start : Nat)
  (hbound : start + 427 ≤ containing.length)
  (hcode : ∀ position < 427, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode hq hl

theorem initialize_phase (state : NatState) (hspec : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing 35 state
    OuterReady q full 0 (5 * (start + 35)) result ∧ Frame q full state result := by
  rw [run_initBlock _ containing start hbound hcode state (by simpa only [Nat.add_zero] using hpc) ha]
  apply init_heap_ready q full hq hl (5 * (start + 35)) hspec (initBlock_heap q full state) ?_
    ((runOps_halted _ _ _).trans ha)
  rw [runOps_pc _ _ _ (by
    dsimp [initBlock, RawCandidateSerializedInputRAM.setCache, setFlat, storeFlat,
      RawCandidateSerializedInputRAM.storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]
    simp), initBlock_length, hpc]
  omega

theorem row_initialize (node : Nat) (state : NatState)
    (ready : OuterReady q full node (5 * (start + 35)) state) (hn : node < size q full) :
    let result := natRun (rawIncidenceROM q full) containing 92 state
    InnerReady q full node 0 (5 * (start + 127)) result ∧ Frame q full state result := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (boundedTest 1 5 (start + 427)) state
  have ht := boundedTest_values q full 1 5 (start + 427) state
  dsimp only at ht
  have hth : tested.heap = state.heap := ht.1
  have htp : tested.pc = 5 * (start + 55) := by
    have hp := ht.2.1
    rw [ready.input.header5, ready.node_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hn), ready.pc] at hp
    dsimp only [tested]
    omega
  have hta : tested.halted = false := ht.2.2.trans ready.active
  have rt : OuterReady q full node (5 * (start + 55)) tested := ready.of_heap_eq hth htp hta
  let finished := runOps rom initRow tested
  have hfh : finished.heap = Function.update (Function.update
      (Function.update tested.heap (internalStart q full + node) (parentWords q full node))
      (workspaceBase full.length q + 3) 0) (workspaceBase full.length q + 2) 0 := by
    have hh := initRow_heap q full tested
    rw [rt.input.header0, rt.node_cell, rt.input.parents node hn] at hh
    exact hh
  have hfp : finished.pc = 5 * (start + 127) := by
    rw [show finished = runOps _ _ _ from rfl, runOps_pc _ _ _ (by
      dsimp [initRow, writeParent, loadParent, RawCandidateSerializedInputRAM.loadCache,
        RawCandidateSerializedInputRAM.setCache, RawCandidateSerializedInputRAM.storeCache,
        RawCandidateWorkspaceBaseRAM.program, loadCell, NoJump]
      simp), initRow_length, htp]
    omega
  have hfa : finished.halted = false := (runOps_halted _ _ _).trans hta
  have hr := row_init_heap_ready q full hq hl node _ _ rt hn hfh hfp hfa
  have hrun : natRun rom containing 92 state = finished := by
    rw [show 92 = 20 + 72 from rfl, natRun_add,
      run_outerTest rom containing start hbound hcode state ready.pc ready.active]
    exact run_initRow rom containing start hbound hcode tested htp hta
  dsimp only
  rw [hrun]
  exact ⟨hr.1, (frame_of_heap_eq q full hth).trans hr.2⟩

theorem child_iteration (node child : Nat) (state : NatState)
    (ready : InnerReady q full node child (5 * (start + 127)) state)
    (hn : node < size q full) (hc : child < size q full) :
    let result := natRun (rawIncidenceROM q full) containing (bitSteps (parentWords q full) node child) state
    InnerReady q full node (child + 1) (5 * (start + 127)) result ∧ Frame q full state result := by
  have hi := inner_iteration q full containing start hbound hcode node child state ready.cursor hc (by
    intro heq
    rw [ready.flat_cell]
    exact (matched_position_lt q full node child hn hc heq).trans (endAddress_lt_base q full hq hl))
  dsimp only at hi
  exact bit_heap_ready q full hq hl node child _ _ ready hn hc hi.1 hi.2.1 hi.2.2

theorem child_scan_partial (node : Nat) (state : NatState)
    (ready : InnerReady q full node 0 (5 * (start + 127)) state) (hn : node < size q full)
    (count : Nat) (hcount : count ≤ size q full) :
    let result := natRun (rawIncidenceROM q full) containing (childSteps q full node count) state
    InnerReady q full node count (5 * (start + 127)) result ∧ Frame q full state result := by
  revert hcount
  induction count with
  | zero =>
    intro _
    simpa only [childSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show InnerReady q full node 0 (5 * (start + 127)) state ∧ Frame q full state state from
        ⟨ready, Frame.refl _ _ state⟩)
  | succ count ih =>
    intro hcount
    rcases ih (by omega) with ⟨rp, hfp⟩
    let previous := natRun (rawIncidenceROM q full) containing (childSteps q full node count) state
    have hs := child_iteration q full hq hl containing start hbound hcode node count previous rp hn (by omega)
    dsimp only at hs
    dsimp only
    rw [childSteps_succ, natRun_add]
    exact ⟨hs.1, hfp.trans hs.2⟩

theorem child_scan (node : Nat) (state : NatState)
    (ready : InnerReady q full node 0 (5 * (start + 127)) state) (hn : node < size q full) :
    let result := natRun (rawIncidenceROM q full) containing (childSteps q full node (size q full) + 20) state
    InnerReady q full node (size q full) (5 * (start + 353)) result ∧ Frame q full state result := by
  let previous := natRun (rawIncidenceROM q full) containing (childSteps q full node (size q full)) state
  rcases child_scan_partial q full hq hl containing start hbound hcode node state ready hn (size q full) le_rfl with ⟨rp, hfp⟩
  let finished := runOps (rawIncidenceROM q full) (boundedTest 2 5 (start + 353)) previous
  have ht := boundedTest_values q full 2 5 (start + 353) previous
  dsimp only at ht
  have hh : finished.heap = previous.heap := ht.1
  have hp : finished.pc = 5 * (start + 353) := by
    have hh := ht.2.1
    rw [rp.cursor.input.header5, rp.cursor.child_cell, Nat.sub_self] at hh
    exact hh
  have ha : finished.halted = false := ht.2.2.trans rp.cursor.active
  dsimp only
  rw [natRun_add, run_innerTest _ containing start hbound hcode previous rp.cursor.pc rp.cursor.active]
  exact ⟨rp.of_heap_eq hh hp ha, hfp.trans (frame_of_heap_eq q full hh)⟩

theorem row_finish (node : Nat) (state : NatState)
    (ready : InnerReady q full node (size q full) (5 * (start + 353)) state) (hn : node < size q full) :
    let result := natRun (rawIncidenceROM q full) containing 74 state
    OuterReady q full (node + 1) (5 * (start + 35)) result ∧ Frame q full state result := by
  have hend := endAddress_lt_base q full hq hl
  have hspan : internalStart q full + 2 * size q full ≤ endAddress q full := by
    unfold endAddress childrenStart
    omega
  have hsep : 3 + state.heap 0 + state.heap 5 + state.heap (workspaceBase full.length q + 1) < workspaceBase full.length q := by
    rw [ready.cursor.input.header0, ready.cursor.input.header5, ready.cursor.node_cell]
    change internalStart q full + size q full + node < _
    omega
  have ht := outerTail_values q full start state hsep
  dsimp only at ht
  have hh := ht.1
  rw [ready.cursor.input.header0, ready.cursor.input.header5, ready.cursor.node_cell, ready.degree_cell] at hh
  rw [run_outerTail _ containing start hbound hcode state ready.cursor.pc ready.cursor.active]
  exact row_finish_heap_ready q full hq hl node _ _ ready hn hh ht.2.1 (ht.2.2.trans ready.cursor.active)

theorem row_iteration (node : Nat) (state : NatState)
    (ready : OuterReady q full node (5 * (start + 35)) state) (hn : node < size q full) :
    let result := natRun (rawIncidenceROM q full) containing (rowSteps q full node) state
    OuterReady q full (node + 1) (5 * (start + 35)) result ∧ Frame q full state result := by
  let initialized := natRun (rawIncidenceROM q full) containing 92 state
  rcases row_initialize q full hq hl containing start hbound hcode node state ready hn with ⟨ri, hfi⟩
  let scanned := natRun (rawIncidenceROM q full) containing (childSteps q full node (size q full) + 20) initialized
  rcases child_scan q full hq hl containing start hbound hcode node initialized ri hn with ⟨rs, hfs⟩
  have hf := row_finish q full hq hl containing start hbound hcode node scanned rs hn
  dsimp only at hf
  dsimp only
  rw [show rowSteps q full node = 92 + ((childSteps q full node (size q full) + 20) + 74) by
    unfold rowSteps
    omega, natRun_add, natRun_add]
  exact ⟨hf.1, (hfi.trans hfs).trans hf.2⟩

theorem outer_scan_partial (state : NatState)
    (ready : OuterReady q full 0 (5 * (start + 35)) state)
    (count : Nat) (hcount : count ≤ size q full) :
    let result := natRun (rawIncidenceROM q full) containing (outerSteps q full count) state
    OuterReady q full count (5 * (start + 35)) result ∧ Frame q full state result := by
  revert hcount
  induction count with
  | zero =>
    intro _
    simpa only [outerSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show OuterReady q full 0 (5 * (start + 35)) state ∧ Frame q full state state from
        ⟨ready, Frame.refl _ _ state⟩)
  | succ count ih =>
    intro hcount
    rcases ih (by omega) with ⟨rp, hfp⟩
    let previous := natRun (rawIncidenceROM q full) containing (outerSteps q full count) state
    have hs := row_iteration q full hq hl containing start hbound hcode count previous rp (by omega)
    dsimp only at hs
    dsimp only
    rw [outerSteps_succ, natRun_add]
    exact ⟨hs.1, hfp.trans hs.2⟩

theorem serialize_phase (state : NatState)
    (hspec : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps q full) state
    OuterReady q full (size q full) (5 * (start + 427)) result ∧ Frame q full state result := by
  let initialized := natRun (rawIncidenceROM q full) containing 35 state
  rcases initialize_phase q full hq hl containing start hbound hcode state hspec hpc hactive with ⟨ri, hfi⟩
  let previous := natRun (rawIncidenceROM q full) containing (outerSteps q full (size q full)) initialized
  rcases outer_scan_partial q full hq hl containing start hbound hcode initialized ri (size q full) le_rfl with ⟨rp, hfp⟩
  let finished := runOps (rawIncidenceROM q full) (boundedTest 1 5 (start + 427)) previous
  have ht := boundedTest_values q full 1 5 (start + 427) previous
  dsimp only at ht
  have hh : finished.heap = previous.heap := ht.1
  have hp : finished.pc = 5 * (start + 427) := by
    have hh := ht.2.1
    rw [rp.input.header5, rp.node_cell, Nat.sub_self] at hh
    exact hh
  have ha : finished.halted = false := ht.2.2.trans rp.active
  have hrun : natRun (rawIncidenceROM q full) containing (totalSteps q full) state = finished := by
    rw [totalSteps, Nat.add_assoc, natRun_add, natRun_add]
    exact run_outerTest _ containing start hbound hcode previous rp.pc rp.active
  dsimp only
  rw [hrun]
  exact ⟨rp.of_heap_eq hh hp ha, (hfi.trans hfp).trans (frame_of_heap_eq q full hh)⟩

end Linked

theorem childSteps_le (q : Nat) (full : List (Finset (Fin q))) (node count : Nat) :
    childSteps q full node count ≤ 223 * count := by
  calc
    _ ≤ ∑ _child ∈ Finset.range count, 223 := by
      apply Finset.sum_le_sum
      intro child _hchild
      unfold bitSteps
      split <;> omega
    _ = _ := by simp [Nat.mul_comm]

theorem outerSteps_le (q : Nat) (full : List (Finset (Fin q))) (count : Nat) :
    outerSteps q full count ≤ count * (186 + 223 * size q full) := by
  calc
    _ ≤ ∑ _node ∈ Finset.range count, (186 + 223 * size q full) := by
      apply Finset.sum_le_sum
      intro node _hnode
      have h := childSteps_le q full node (size q full)
      unfold rowSteps
      omega
    _ = _ := by simp

theorem totalSteps_le (q : Nat) (full : List (Finset (Fin q))) :
    totalSteps q full ≤ 512 * (size q full + 1) ^ 2 := by
  have h := outerSteps_le q full (size q full)
  unfold totalSteps
  nlinarith

structure Output (q : Nat) (full : List (Finset (Fin q))) (pointer : Nat) (before after : NatState) : Prop where
  input : RawCandidateSerializedChildrenRAM.InputSpec q full after
  internal : ∀ position < (givenTreeROM q full).internal.length,
    after.heap (internalStart q full + position) = (givenTreeROM q full).internal.getD position 0
  children : Written (childrenStart q full) (givenTreeROM q full).children after
  frame : Frame q full before after
  node_cell : after.heap (workspaceBase full.length q + 1) = size q full
  flat_cell : after.heap (flatAddress full.length q) = (givenTreeROM q full).children.length
  pc : after.pc = pointer
  active : after.halted = false

theorem Output.of_ready (q : Nat) (full : List (Finset (Fin q))) (pointer : Nat) {before after : NatState}
    (ready : OuterReady q full (size q full) pointer after) (hf : Frame q full before after) :
    Output q full pointer before after := by
  refine ⟨ready.input, ?_, ?_, hf, ready.node_cell, ?_, ready.pc, ready.active⟩
  · intro position hposition
    have ht : position < 2 * size q full := by
      simpa only [RawTreeSerialization.givenTreeROM_internal_length, size] using hposition
    by_cases hp : position < size q full
    · exact ready.parents position hp
    · let parent := position - size q full
      have hparent : parent < size q full := by dsimp only [parent]; omega
      have heq : position = size q full + parent := by dsimp only [parent]; omega
      rw [heq, show internalStart q full + (size q full + parent) = internalStart q full + size q full + parent by omega,
        ready.degrees parent hparent]
      exact childIDs_length_eq_internalWord q full (parentWords q full)
        (givenTreeROM_parentWords q full) ⟨parent, hparent⟩
  · have h := ready.children
    rwa [beforeList_full] at h
  · have h := ready.flat_cell
    rwa [beforeList_full] at h

theorem Output.prefix_frame {q : Nat} {full : List (Finset (Fin q))} {pointer : Nat} {before after : NatState}
    (output : Output q full pointer before after) (hq : 0 < q) (hl : LaminarSchedule full) :
    ∀ address < internalStart q full, after.heap address = before.heap address := by
  have hend := endAddress_lt_base q full hq hl
  have hspan : internalStart q full ≤ endAddress q full := by unfold endAddress childrenStart; omega
  intro address ha
  apply output.frame
  unfold Protected
  have hf : workspaceBase full.length q + 5 ≤ flatAddress full.length q := by unfold flatAddress; omega
  exact ⟨by omega, by omega, by omega, by omega, Or.inl ha⟩

theorem serialize (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (containing : List PackingOp) (start : Nat) (hbound : start + 427 ≤ containing.length)
    (hcode : ∀ position < 427, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)
    (state : NatState) (hspec : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Output q full (5 * (start + 427)) state
      (natRun (rawIncidenceROM q full) containing (totalSteps q full) state) := by
  rcases serialize_phase q full hq hl containing start hbound hcode state hspec hpc hactive with ⟨ready, hf⟩
  exact Output.of_ready q full _ ready hf

theorem append_slice (left right : List PackingOp) :
    left.length + 427 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 427,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  refine ⟨by simp only [List.length_append, programAt_length]; omega, ?_⟩
  intro position hp
  rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]
      omega),
    List.getD_append_right left (programAt left.length) paddingOp _ (by omega),
    Nat.add_sub_cancel_left]

theorem serialize_append (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (left right : List PackingOp) (state : NatState) (hspec : RawCandidateSerializedChildrenRAM.InputSpec q full state)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    Output q full (5 * (left.length + 427)) state
      (natRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right) (totalSteps q full) state) :=
  serialize q full hq hl _ left.length (append_slice left right).1 (append_slice left right).2 state hspec hpc hactive

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenRun
