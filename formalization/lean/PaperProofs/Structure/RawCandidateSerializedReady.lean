module

public import PaperProofs.Structure.RawCandidateSerializedInputRAM
public import PaperProofs.Structure.RawCandidateSerializedInputLayout

/-! Shared runtime handoffs for the raw-copy and node-bit loops.  No loop
termination or incidence answer is an input to these state predicates. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedReady

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateWorkspaceInit RawCandidateSerializedInputRAM

def HeaderSpec (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ position < 6, state.heap position =
    [3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q,
      2 * (prepareNormalization q full).indexed.nodes.size,
      (prepareNormalization q full).indexed.nodes.size - 1,
      full.length, q, (prepareNormalization q full).indexed.nodes.size].getD position 0

theorem HeaderSpec.tools {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : HeaderSpec q full state) : state.heap 4 = q := by
  simpa using h 4 (by decide)

theorem HeaderSpec.count {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : HeaderSpec q full state) : state.heap 5 = (prepareNormalization q full).indexed.nodes.size := by
  simpa using h 5 (by decide)

theorem HeaderSpec.stages {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : HeaderSpec q full state) : state.heap 3 = full.length := by
  simpa using h 3 (by decide)

theorem HeaderSpec.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : HeaderSpec q full before) (hh : after.heap = before.heap) : HeaderSpec q full after := by
  intro position hp
  exact (congrFun hh position).trans (h position hp)

theorem HeaderSpec.prefix {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (h : HeaderSpec q full state) (position : Nat) (hp : position < 6) :
    state.heap position = (RawCandidateSerializedInputLayout.prefixWords q full).getD position 0 :=
  (h position hp).trans (RawCandidateSerializedInputLayout.prefixWords_getD_header q full position hp).symm

structure StageReady (q : Nat) (full : List (Finset (Fin q))) (pointer : Nat) (state : NatState) : Prop where
  headers : HeaderSpec q full state
  input : InputSpec q full state
  raw_count : state.heap (workspaceBase full.length q + 3) = full.length * q
  pc : state.pc = pointer
  active : state.halted = false

structure RawReady (q : Nat) (full : List (Finset (Fin q))) (offset pointer : Nat) (state : NatState) : Prop where
  stage : StageReady q full pointer state
  cursor : state.heap (workspaceBase full.length q + 1) = offset

structure NodeReady (q : Nat) (full : List (Finset (Fin q))) (node pointer : Nat) (state : NatState) : Prop where
  stage : StageReady q full pointer state
  node_cell : state.heap (workspaceBase full.length q + 1) = node

structure ToolReady (q : Nat) (full : List (Finset (Fin q))) (node tool pointer : Nat) (state : NatState) : Prop where
  stage : StageReady q full pointer state
  node_cell : state.heap (workspaceBase full.length q + 1) = node
  tool_cell : state.heap (workspaceBase full.length q + 2) = tool

theorem StageReady.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    {pointer nextPointer : Nat} (h : StageReady q full pointer before) (hh : after.heap = before.heap)
    (hp : after.pc = nextPointer) (ha : after.halted = false) : StageReady q full nextPointer after := by
  refine ⟨HeaderSpec.of_heap_eq h.headers hh, ?_, ?_, hp, ha⟩
  · constructor
    · exact (congrFun hh _).trans h.input.node_count
    · intro node hn
      rw [hh]
      exact h.input.ord_legal node hn
    · intro node hn
      rw [hh]
      exact h.input.ord_support node hn
  · exact (congrFun hh _).trans h.raw_count

theorem aboveFrame_mono (N q beforeBound afterBound : Nat) {before after : NatState}
    (hbound : beforeBound ≤ afterBound) (h : AboveFrame N q beforeBound before after) :
    AboveFrame N q afterBound before after :=
  fun address ha h1 h2 h3 => h address (hbound.trans ha) h1 h2 h3

theorem headers_ready (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 443 ≤ containing.length)
    (hcode : ∀ position < 443, containing.getD (start + position) RawCandidateSerializedInputRAM.paddingOp =
      (programAt start).getD position RawCandidateSerializedInputRAM.paddingOp)
    (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    let result := natRun (rawIncidenceROM q full) containing 79 state
    StageReady q full (5 * (start + 79)) result ∧ AboveFrame full.length q 6 state result := by
  have hb := workspaceBase_ge full.length q
  rw [run_headers (rawIncidenceROM q full) containing start hbound hcode state hpc hactive]
  have hf := headers_aboveFrame q full state
  refine ⟨?_, hf⟩
  constructor
  · intro position hp
    rw [headers_heap, hinput.node_count]
    interval_cases position <;> simp (disch := omega) [headerHeap]
  · exact InputSpec.of_aboveFrame q full 6 hinput (by omega) hf
  · rw [headers_heap]
    simp (disch := omega) [headerHeap]
  · rw [runOps_pc _ _ _ (by
      simp [headers, loadNodeCount, loadCache, storeCache, RawCandidateWorkspaceBaseRAM.program,
        loadCell, storeCell, NoJump]), headers_length, hpc]
    omega
  · rw [runOps_halted, hactive]

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedReady
