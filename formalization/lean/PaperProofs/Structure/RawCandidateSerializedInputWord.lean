module

public import PaperProofs.Structure.RawCandidateSerializedInputWordDataPieces
public import PaperProofs.Structure.RawCandidateSerializedInputWordHeaders

/-! Complete fetched-prefix safety for the original input serializer.
All controls are initialized by the executed code; cache accesses recover
their base from the readonly raw dimensions rather than output cell eight. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedInputRAM RawCandidateSerializedReady
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawCandidateSerializedInputWordChunks (Chunk chunkCode chunkOffset chunkLength SafePoint chunk_of_macro chunk_run kernel_safe)
open RawCandidateSerializedInputRun (nodeDestination nodeBitSteps toolScanSteps rowSteps nodeScanSteps)

theorem small_fits (N q value : Nat) (hv : value ≤ candidateCount N q) : Fits (indexWidth 16 N q) value :=
  hv.trans_lt (candidateCount_fits N q)

theorem size_le (q : Nat) (full : List (Finset (Fin q))) :
    (prepareNormalization q full).indexed.nodes.size ≤ candidateCount full.length q := prepared_indexed_size_le q full

theorem input_count_le {q : Nat} {full : List (Finset (Fin q))} {state : NatState} (input : InputSpec q full state) :
    state.heap (nodeCountAddress full.length q) ≤ candidateCount full.length q := by
  rw [input.node_count]
  exact size_le q full

theorem ord_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState} (input : InputSpec q full state)
    (node : Nat) (hn : node < (prepareNormalization q full).indexed.nodes.size) :
    Fits (indexWidth 16 full.length q) (state.heap (ordAddress full.length q node)) :=
  small_fits _ _ _ (input.ord_legal node hn).le

theorem q_fits (N q : Nat) : Fits (indexWidth 16 N q) q := small_fits N q q (by unfold candidateCount; omega)

theorem stage_raw_fits {q : Nat} {full : List (Finset (Fin q))} {pointer : Nat} {state : NatState}
    (ready : StageReady q full pointer state) :
    Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + 3)) := by
  rw [ready.raw_count]
  exact RawCandidateSerializedInputWordDataPieces.raw_product_fits _ _

theorem header_tools_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState} (headers : HeaderSpec q full state) :
    Fits (indexWidth 16 full.length q) (state.heap 4) := by rw [headers.tools]; exact q_fits _ _

theorem header_count_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState} (headers : HeaderSpec q full state) :
    Fits (indexWidth 16 full.length q) (state.heap 5) := by rw [headers.count]; exact small_fits _ _ _ (size_le q full)

theorem frame_ord {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (frame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after) (node : Nat) :
    after.heap (ordAddress full.length q node) = before.heap (ordAddress full.length q node) := by
  have hp : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
  exact frame _ (by unfold ordAddress; omega) (by unfold ordAddress; omega)
    (by unfold ordAddress; omega) (by unfold ordAddress; omega)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 443 ≤ containing.length)
  (hcode : ∀ position < 443, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem raw_iteration_safe (offset : Nat) (state : NatState)
    (ready : RawReady q full offset (5 * (start + 95)) state) (hoffset : offset < full.length * q)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 89 ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing 89 state) := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (rawTest (start + 184)) state
  have tv := rawTest_values q full (start + 184) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 128) := by
    have hp := tv.2.1
    rw [ready.stage.raw_count, ready.cursor, ite_eq_right (Nat.sub_ne_zero_of_lt hoffset), ready.stage.pc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := tv.2.2.trans ready.stage.active
  have ts := chunk_of_macro q full containing start hbound hcode .rawTest state ready.stage.pc ready.stage.active
    (RawCandidateSerializedInputWordPieces.rawTest_safe q full (start + 184) state hf
      (by rw [ready.cursor]; exact hoffset.le.trans_lt (RawCandidateSerializedInputWordDataPieces.raw_product_fits _ _))
      (stage_raw_fits ready.stage) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .rawTest state ready.stage.pc ready.stage.active] at ts
  have bs := chunk_of_macro q full containing start hbound hcode .rawBody tested tp ta
    (RawCandidateSerializedInputWordDataPieces.rawBody_safe q full start tested ts.2
      (by rw [th, ready.cursor]; exact hoffset) hend)
  dsimp only [chunkLength] at ts bs
  have runTest : natRun rom containing 33 state = tested := chunk_run q full containing start hbound hcode .rawTest state ready.stage.pc ready.stage.active
  constructor
  · change PrefixSafe _ _ _ _ (33 + 56)
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact bs.1
  · rw [show 89 = 33 + 56 by decide, natRun_add, runTest]
    exact bs.2

theorem raw_partial_safe (state : NatState) (ready : RawReady q full 0 (5 * (start + 95)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) (count : Nat) (hc : count ≤ full.length * q) :
    let result := natRun (rawIncidenceROM q full) containing (89 * count) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (89 * count) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ RawReady q full count (5 * (start + 95)) result := by
  revert hc
  induction count with
  | zero => intro _; exact ⟨by intro clock hc; omega, hf, ready⟩
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits, previousReady⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (89 * count) state
    have step := raw_iteration_safe q full containing start hbound hcode count previous previousReady (by omega) fits hend
    have data := RawCandidateSerializedRawCopy.raw_iteration q full containing start hbound hcode count (by omega) previous previousReady
    constructor
    · rw [Nat.mul_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [Nat.mul_succ, natRun_add]
      exact ⟨step.2, data.1⟩

theorem copy_raw_safe (state : NatState) (ready : StageReady q full (5 * (start + 79)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (89 * (full.length * q) + 49) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (89 * (full.length * q) + 49) state) := by
  let rom := rawIncidenceROM q full
  let initialized := natRun rom containing 16 state
  have ini := chunk_of_macro q full containing start hbound hcode .rawInit state ready.pc ready.active
    (RawCandidateSerializedInputWordCache.setCache_safe q full 1 0 (by omega) state hf (small_fits _ _ _ (by omega)))
  have ir := (RawCandidateSerializedRawCopy.raw_init q full containing start hbound hcode state ready).1
  have scan := raw_partial_safe q full containing start hbound hcode initialized ir ini.2 hend (full.length * q) le_rfl
  let previous := natRun rom containing (89 * (full.length * q)) initialized
  have pr := scan.2.2
  have ts := chunk_of_macro q full containing start hbound hcode .rawTest previous pr.stage.pc pr.stage.active
    (RawCandidateSerializedInputWordPieces.rawTest_safe q full (start + 184) previous scan.2.1
      (by rw [pr.cursor]; exact RawCandidateSerializedInputWordDataPieces.raw_product_fits _ _)
      (stage_raw_fits pr.stage) (lt_of_le_of_lt (by omega) hend))
  dsimp only [chunkLength] at ini ts
  have body : PrefixSafe (SafePoint q full containing start) rom containing initialized (89 * (full.length * q) + 33) :=
    PrefixSafe.add _ _ _ _ _ _ scan.1 ts.1
  have hclock : 89 * (full.length * q) + 49 = 16 + (89 * (full.length * q) + 33) := by omega
  constructor
  · rw [hclock]
    exact PrefixSafe.add _ _ _ _ _ _ ini.1 body
  · rw [hclock, natRun_add, natRun_add]
    exact ts.2

theorem node_bit_iteration_safe (node tool : Nat) (state : NatState)
    (ready : ToolReady q full node tool (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size) (ht : tool < q)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (nodeBitSteps full.length candidate tool) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (nodeBitSteps full.length candidate tool) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ ToolReady q full node (tool + 1) (5 * (start + 236)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let candidate := state.heap (ordAddress full.length q node)
  have hc : candidate < full.length + q + 1 := ready.stage.input.ord_legal node hn
  have hm := size_le q full
  let tested := runOps rom (boundedTest 2 4 (start + 408)) state
  have tv := boundedTest_values q full 2 4 (start + 408) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 256) := by
    have hp := tv.2.1
    rw [ready.stage.headers.tools, ready.tool_cell, ite_eq_right (Nat.sub_ne_zero_of_lt ht), ready.stage.pc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := tv.2.2.trans ready.stage.active
  have ts := chunk_of_macro q full containing start hbound hcode .toolTest state ready.stage.pc ready.stage.active
    (RawCandidateSerializedInputWordPieces.boundedTest_safe q full 2 4 (start + 408) (by omega) (by omega) state hf
      (by rw [ready.tool_cell]; exact ht.le.trans_lt (q_fits _ _))
      (header_tools_fits ready.stage.headers) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .toolTest state ready.stage.pc ready.stage.active] at ts
  let args := runOps rom arguments tested
  have av := arguments_values q full tested
  have ao : args.register .old = candidate := by simpa only [th, ready.node_cell] using av.1
  have af : args.register .fresh = tool := by simpa only [th, ready.tool_cell] using av.2.1
  have ah : args.heap = state.heap := av.2.2.1.trans th
  have ap : args.pc = 5 * (start + 305) := by
    have hp := av.2.2.2.1
    rw [tp] at hp
    change args.pc = _ at hp
    omega
  have aa : args.halted = false := av.2.2.2.2.trans ta
  have asafe := chunk_of_macro q full containing start hbound hcode .arguments tested tp ta
    (RawCandidateSerializedInputWordDataPieces.arguments_safe q full tested ts.2
      (by rw [th, ready.node_cell]; omega)
      (by rw [th, ready.node_cell]; exact ord_fits ready.stage.input node hn)
      (by rw [th, ready.tool_cell]; exact ht.le.trans_lt (q_fits _ _)))
  rw [chunk_run q full containing start hbound hcode .arguments tested tp ta] at asafe
  have kernel := kernel_safe q full containing start hbound hcode ⟨candidate, hc⟩ ⟨tool, ht⟩ args ap aa ao af asafe.2 hend
  let steps := RawCandidateIncidenceWord.steps full.length candidate tool
  let queried := natRun rom containing steps args
  obtain ⟨_answer, _old, fresh, heap, pcQuery, activeQuery⟩ := kernel.2.2
  have qh : queried.heap = state.heap := heap.trans ah
  have qf : queried.register .fresh = tool := fresh.trans af
  have qn : queried.heap (workspaceBase full.length q + 1) = node := (congrFun qh _).trans ready.node_cell
  have qt : queried.heap (workspaceBase full.length q + 2) = tool := (congrFun qh _).trans ready.tool_cell
  have qr : queried.heap (workspaceBase full.length q + 3) = full.length * q := (congrFun qh _).trans ready.stage.raw_count
  have qp : queried.pc = 5 * (start + 337) := by simpa only [Nat.add_assoc] using pcQuery
  have tm := RawCandidateSerializedInputWordDataPieces.toolTail_safe q full start queried kernel.2.1
    (by rw [qn]; omega) (by rw [qf]; exact ht.le) qr.le (by rw [qt]; exact ht.le) hend
  have tail := chunk_of_macro q full containing start hbound hcode .toolTail queried qp activeQuery tm
  have hsep : 6 + queried.heap (workspaceBase full.length q + 3) +
      queried.heap (workspaceBase full.length q + 1) * q + queried.register .fresh < workspaceBase full.length q := by
    rw [qr, qn, qf]
    exact (RawCandidateSerializedInputRun.nodeDestination_lt_prefix q full node tool hn ht).trans (prefixLength_lt_base q full)
  let finished := runOps rom (toolTail start) queried
  have tvTail := toolTail_values q full start queried hsep
  have fh : finished.heap = Function.update
      (Function.update state.heap (nodeDestination q full node tool) (queried.register .value))
      (workspaceBase full.length q + 2) (tool + 1) := by
    have hh := tvTail.1
    rw [qr, qn, qf, qt, qh] at hh
    exact hh
  have fr := RawCandidateSerializedInputRun.tool_heap_ready q full node tool (5 * (start + 236)) (5 * (start + 236))
    (queried.register .value) ready hn ht fh tvTail.2.1 (tvTail.2.2.trans activeQuery)
  dsimp only [chunkLength] at ts asafe tail
  have runTest : natRun rom containing 20 state = tested := chunk_run q full containing start hbound hcode .toolTest state ready.stage.pc ready.stage.active
  have runArgs : natRun rom containing 49 tested = args := chunk_run q full containing start hbound hcode .arguments tested tp ta
  have runTail : natRun rom containing 71 queried = finished := chunk_run q full containing start hbound hcode .toolTail queried qp activeQuery
  have hclock : nodeBitSteps full.length candidate tool = 20 + (49 + (steps + 71)) := by
    unfold RawCandidateSerializedInputRun.nodeBitSteps
    dsimp [steps, RawCandidateIncidenceWord.steps]
    omega
  have whole : natRun rom containing (nodeBitSteps full.length candidate tool) state = finished := by
    rw [hclock, natRun_add, runTest, natRun_add, runArgs, natRun_add]
    exact runTail
  have kr : PrefixSafe (SafePoint q full containing start) rom containing args (steps + 71) :=
    PrefixSafe.add _ _ _ _ _ _ kernel.1 tail.1
  have ar : PrefixSafe (SafePoint q full containing start) rom containing tested (49 + (steps + 71)) := by
    apply PrefixSafe.add _ _ _ _ _ _ asafe.1
    rw [runArgs]
    exact kr
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state (nodeBitSteps full.length candidate tool) := by
    rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact ar
  dsimp only
  refine ⟨allSafe, ?_, ?_, ?_⟩
  · rw [whole]
    have fits := tail.2
    rwa [runTail] at fits
  · rw [whole]
    exact fr.1
  · rw [whole]
    exact fr.2.1

theorem tool_scan_partial_safe (node : Nat) (state : NatState)
    (ready : ToolReady q full node 0 (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) (count : Nat) (hc : count ≤ q) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (toolScanSteps full.length candidate count) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (toolScanSteps full.length candidate count) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ ToolReady q full node count (5 * (start + 236)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [RawCandidateSerializedInputRun.toolScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state ∧ ToolReady q full node 0 (5 * (start + 236)) state ∧
        AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state state from
          ⟨by intro clock hc; omega, hf, ready, AboveFrame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits, rp, frame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing
      (toolScanSteps full.length (state.heap (ordAddress full.length q node)) count) state
    have step := node_bit_iteration_safe q full containing start hbound hcode node count previous rp hn (by omega) fits hend
    dsimp only at step
    have preserved := frame_ord frame node
    rw [preserved] at step
    constructor
    · rw [RawCandidateSerializedInputRun.toolScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [RawCandidateSerializedInputRun.toolScanSteps_succ, natRun_add]
      exact ⟨step.2.1, step.2.2.1, AboveFrame.trans _ _ _ frame step.2.2.2⟩

theorem tool_scan_safe (node : Nat) (state : NatState)
    (ready : ToolReady q full node 0 (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (toolScanSteps full.length candidate q + 20) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (toolScanSteps full.length candidate q + 20) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ ToolReady q full node q (5 * (start + 408)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  have scan := tool_scan_partial_safe q full containing start hbound hcode node state ready hn hf hend q le_rfl
  let previous := natRun rom containing (toolScanSteps full.length (state.heap (ordAddress full.length q node)) q) state
  have rp : ToolReady q full node q (5 * (start + 236)) previous := scan.2.2.1
  have tv := boundedTest_values q full 2 4 (start + 408) previous
  let tested := runOps rom (boundedTest 2 4 (start + 408)) previous
  have th : tested.heap = previous.heap := tv.1
  have tp : tested.pc = 5 * (start + 408) := by
    simpa only [rp.stage.headers.tools, rp.tool_cell, Nat.sub_self, ite_true] using tv.2.1
  have ta : tested.halted = false := tv.2.2.trans rp.stage.active
  have tr : ToolReady q full node q (5 * (start + 408)) tested :=
    ⟨rp.stage.of_heap_eq th tp ta, (congrFun th _).trans rp.node_cell, (congrFun th _).trans rp.tool_cell⟩
  have ts := chunk_of_macro q full containing start hbound hcode .toolTest previous rp.stage.pc rp.stage.active
    (RawCandidateSerializedInputWordPieces.boundedTest_safe q full 2 4 (start + 408) (by omega) (by omega) previous scan.2.1
      (by rw [rp.tool_cell]; exact q_fits _ _) (header_tools_fits rp.stage.headers) (lt_of_le_of_lt (by omega) hend))
  dsimp only [chunkLength] at ts
  have runTest : natRun rom containing 20 previous = tested := chunk_run q full containing start hbound hcode .toolTest previous rp.stage.pc rp.stage.active
  have frame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state tested := by
    intro address ha h1 h2 h3
    exact (congrFun th address).trans (scan.2.2.2 address ha h1 h2 h3)
  dsimp only
  refine ⟨PrefixSafe.add _ _ _ _ _ _ scan.1 ts.1, ?_⟩
  rw [natRun_add, runTest]
  refine ⟨?_, tr, frame⟩
  have fits := ts.2
  rwa [runTest] at fits

theorem node_init_safe (state : NatState) (ready : StageReady q full (5 * (start + 184)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state) :
    let result := natRun (rawIncidenceROM q full) containing 16 state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 16 ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ NodeReady q full 0 (5 * (start + 200)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setCache 1 0) state
  have ih := setCache_heap q full 1 0 state
  have ip : initialized.pc = 5 * (start + 200) := by
    rw [show initialized = runOps rom (setCache 1 0) state from rfl,
      runOps_pc rom (setCache 1 0) state (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]),
      setCache_length, ready.pc]
    omega
  have ia : initialized.halted = false := (runOps_halted _ _ _).trans ready.active
  have control := RawCandidateSerializedInputRun.control_update_ready q full (5 * (start + 184)) (5 * (start + 200)) 1 0
    ready (Or.inl rfl) ih ip ia
  have resultReady : NodeReady q full 0 (5 * (start + 200)) initialized :=
    ⟨control.1, by change (runOps rom (setCache 1 0) state).heap _ = _; rw [ih]; simp⟩
  have safe := chunk_of_macro q full containing start hbound hcode .nodeInit state ready.pc ready.active
    (RawCandidateSerializedInputWordCache.setCache_safe q full 1 0 (by omega) state hf (small_fits _ _ _ (by omega)))
  have runInit : natRun rom containing 16 state = initialized := chunk_run q full containing start hbound hcode .nodeInit state ready.pc ready.active
  dsimp only [chunkLength] at safe
  dsimp only
  refine ⟨safe.1, safe.2, ?_, ?_⟩ <;> rw [runInit]
  · exact resultReady
  · exact control.2.1

theorem tool_init_safe (node : Nat) (state : NatState) (ready : NodeReady q full node (5 * (start + 220)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state) :
    let result := natRun (rawIncidenceROM q full) containing 16 state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 16 ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ ToolReady q full node 0 (5 * (start + 236)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom (setCache 2 0) state
  have ih := setCache_heap q full 2 0 state
  have ip : initialized.pc = 5 * (start + 236) := by
    rw [show initialized = runOps rom (setCache 2 0) state from rfl,
      runOps_pc rom (setCache 2 0) state (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]),
      setCache_length, ready.stage.pc]
    omega
  have ia : initialized.halted = false := (runOps_halted _ _ _).trans ready.stage.active
  have control := RawCandidateSerializedInputRun.control_update_ready q full (5 * (start + 220)) (5 * (start + 236)) 2 0
    ready.stage (Or.inr rfl) ih ip ia
  have resultReady : ToolReady q full node 0 (5 * (start + 236)) initialized := by
    refine ⟨control.1, ?_, ?_⟩
    · change (runOps rom (setCache 2 0) state).heap _ = _
      rw [ih, Function.update_of_ne (by omega)]
      exact ready.node_cell
    · change (runOps rom (setCache 2 0) state).heap _ = _
      rw [ih]
      simp
  have safe := chunk_of_macro q full containing start hbound hcode .toolInit state ready.stage.pc ready.stage.active
    (RawCandidateSerializedInputWordCache.setCache_safe q full 2 0 (by omega) state hf (small_fits _ _ _ (by omega)))
  have runInit : natRun rom containing 16 state = initialized := chunk_run q full containing start hbound hcode .toolInit state ready.stage.pc ready.stage.active
  dsimp only [chunkLength] at safe
  dsimp only
  refine ⟨safe.1, safe.2, ?_, ?_⟩ <;> rw [runInit]
  · exact resultReady
  · exact control.2.1

theorem node_iteration_safe (node : Nat) (state : NatState)
    (ready : NodeReady q full node (5 * (start + 200)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (rowSteps full.length q candidate) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (rowSteps full.length q candidate) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ NodeReady q full (node + 1) (5 * (start + 200)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let candidate := state.heap (ordAddress full.length q node)
  have hm := size_le q full
  let tested := runOps rom (boundedTest 1 5 (start + 443)) state
  have tv := boundedTest_values q full 1 5 (start + 443) state
  have th : tested.heap = state.heap := tv.1
  have tp : tested.pc = 5 * (start + 220) := by
    have hp := tv.2.1
    rw [ready.stage.headers.count, ready.node_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hn), ready.stage.pc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := tv.2.2.trans ready.stage.active
  have tr : NodeReady q full node (5 * (start + 220)) tested :=
    ⟨ready.stage.of_heap_eq th tp ta, (congrFun th _).trans ready.node_cell⟩
  have ts := chunk_of_macro q full containing start hbound hcode .nodeTest state ready.stage.pc ready.stage.active
    (RawCandidateSerializedInputWordPieces.boundedTest_safe q full 1 5 (start + 443) (by omega) (by omega) state hf
      (by rw [ready.node_cell]; exact small_fits _ _ _ (hn.le.trans hm))
      (header_count_fits ready.stage.headers) hend)
  rw [chunk_run q full containing start hbound hcode .nodeTest state ready.stage.pc ready.stage.active] at ts
  let initialized := natRun rom containing 16 tested
  have ini := tool_init_safe q full containing start hbound hcode node tested tr ts.2
  have scan := tool_scan_safe q full containing start hbound hcode node initialized ini.2.2.1 hn ini.2.1 hend
  have preserved0 : initialized.heap (ordAddress full.length q node) = candidate :=
    (frame_ord ini.2.2.2 node).trans (congrFun th _)
  rw [preserved0] at scan
  let scanned := natRun rom containing (toolScanSteps full.length candidate q + 20) initialized
  have sr : ToolReady q full node q (5 * (start + 408)) scanned := scan.2.2.1
  have tm := RawCandidateSerializedInputWordDataPieces.rowTail_safe q full start scanned scan.2.1
    (by rw [sr.node_cell]; exact small_fits _ _ _ ((Nat.succ_le_of_lt hn).trans hm)) hend
  have tail := chunk_of_macro q full containing start hbound hcode .rowTail scanned sr.stage.pc sr.stage.active tm
  let finished := runOps rom (rowTail start) scanned
  have tvTail := rowTail_values q full start scanned
  have fh : finished.heap = Function.update scanned.heap (workspaceBase full.length q + 1) (node + 1) := by
    simpa only [sr.node_cell] using tvTail.1
  have control := RawCandidateSerializedInputRun.control_update_ready q full (5 * (start + 408)) (5 * (start + 200)) 1 (node + 1)
    sr.stage (Or.inl rfl) fh tvTail.2.1 (tvTail.2.2.trans sr.stage.active)
  have resultReady : NodeReady q full (node + 1) (5 * (start + 200)) finished :=
    ⟨control.1, by rw [fh]; simp⟩
  have ff : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state finished := by
    apply AboveFrame.trans _ _ _ _ (AboveFrame.trans _ _ _ ini.2.2.2 (AboveFrame.trans _ _ _ scan.2.2.2 control.2.1))
    intro address _ha _h1 _h2 _h3
    exact congrFun th address
  dsimp only [chunkLength] at ts tail
  have runTest : natRun rom containing 20 state = tested := chunk_run q full containing start hbound hcode .nodeTest state ready.stage.pc ready.stage.active
  have runTail : natRun rom containing 35 scanned = finished := chunk_run q full containing start hbound hcode .rowTail scanned sr.stage.pc sr.stage.active
  have hclock : rowSteps full.length q candidate = 20 + (16 + ((toolScanSteps full.length candidate q + 20) + 35)) := by
    unfold RawCandidateSerializedInputRun.rowSteps
    omega
  have whole : natRun rom containing (rowSteps full.length q candidate) state = finished := by
    rw [hclock, natRun_add, runTest, natRun_add, natRun_add]
    exact runTail
  have scanRest : PrefixSafe (SafePoint q full containing start) rom containing initialized
      ((toolScanSteps full.length candidate q + 20) + 35) := PrefixSafe.add _ _ _ _ _ _ scan.1 tail.1
  have initRest : PrefixSafe (SafePoint q full containing start) rom containing tested
      (16 + ((toolScanSteps full.length candidate q + 20) + 35)) := PrefixSafe.add _ _ _ _ _ _ ini.1 scanRest
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact initRest
  · rw [whole]
    have fits := tail.2
    rwa [runTail] at fits
  · rw [whole]
    exact resultReady
  · rw [whole]
    exact ff

theorem node_scan_partial_safe (state : NatState) (ready : NodeReady q full 0 (5 * (start + 200)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443)))
    (count : Nat) (hc : count ≤ (prepareNormalization q full).indexed.nodes.size) :
    let ord := fun node => state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (nodeScanSteps full.length q ord count) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (nodeScanSteps full.length q ord count) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ NodeReady q full count (5 * (start + 200)) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [RawCandidateSerializedInputRun.nodeScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state ∧ NodeReady q full 0 (5 * (start + 200)) state ∧
        AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state state from
          ⟨by intro clock hc; omega, hf, ready, AboveFrame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hc
    obtain ⟨safe, fits, rp, frame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing
      (nodeScanSteps full.length q (fun node => state.heap (ordAddress full.length q node)) count) state
    have step := node_iteration_safe q full containing start hbound hcode count previous rp (by omega) fits hend
    dsimp only at step
    rw [frame_ord frame count] at step
    constructor
    · rw [RawCandidateSerializedInputRun.nodeScanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [RawCandidateSerializedInputRun.nodeScanSteps_succ, natRun_add]
      exact ⟨step.2.1, step.2.2.1, AboveFrame.trans _ _ _ frame step.2.2.2⟩

theorem node_scan_safe (state : NatState) (ready : NodeReady q full 0 (5 * (start + 200)) state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    let ord := fun node => state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing
      (nodeScanSteps full.length q ord (prepareNormalization q full).indexed.nodes.size + 20) state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (nodeScanSteps full.length q ord (prepareNormalization q full).indexed.nodes.size + 20) ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ NodeReady q full (prepareNormalization q full).indexed.nodes.size
        (5 * (start + 443)) result ∧ AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let count := (prepareNormalization q full).indexed.nodes.size
  let ord := fun node => state.heap (ordAddress full.length q node)
  have scan := node_scan_partial_safe q full containing start hbound hcode state ready hf hend count le_rfl
  let previous := natRun rom containing (nodeScanSteps full.length q ord count) state
  have rp : NodeReady q full count (5 * (start + 200)) previous := scan.2.2.1
  let tested := runOps rom (boundedTest 1 5 (start + 443)) previous
  have tv := boundedTest_values q full 1 5 (start + 443) previous
  have th : tested.heap = previous.heap := tv.1
  have tp : tested.pc = 5 * (start + 443) := by
    have hp := tv.2.1
    rw [rp.stage.headers.count, rp.node_cell] at hp
    simpa only [count, Nat.sub_self, ite_true] using hp
  have ta : tested.halted = false := tv.2.2.trans rp.stage.active
  have tr : NodeReady q full count (5 * (start + 443)) tested :=
    ⟨rp.stage.of_heap_eq th tp ta, (congrFun th _).trans rp.node_cell⟩
  have ts := chunk_of_macro q full containing start hbound hcode .nodeTest previous rp.stage.pc rp.stage.active
    (RawCandidateSerializedInputWordPieces.boundedTest_safe q full 1 5 (start + 443) (by omega) (by omega) previous scan.2.1
      (by rw [rp.node_cell]; exact small_fits _ _ _ (size_le q full)) (header_count_fits rp.stage.headers) hend)
  dsimp only [chunkLength] at ts
  have runTest : natRun rom containing 20 previous = tested := chunk_run q full containing start hbound hcode .nodeTest previous rp.stage.pc rp.stage.active
  have frame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state tested := by
    intro address ha h1 h2 h3
    exact (congrFun th address).trans (scan.2.2.2 address ha h1 h2 h3)
  dsimp only
  refine ⟨PrefixSafe.add _ _ _ _ _ _ scan.1 ts.1, ?_⟩
  rw [natRun_add, runTest]
  refine ⟨?_, tr, frame⟩
  have fits := ts.2
  rwa [runTest] at fits

theorem materialize_prefix_nat_safe (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) containing steps state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state steps ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ StageReady q full (5 * (start + 443)) result ∧
      RawCandidateSerializedInputRun.PrefixWritten q full (RawCandidateSerializedInputLayout.prefixLength q full) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let headed := natRun rom containing 79 state
  have hs := chunk_of_macro q full containing start hbound hcode .headers state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha
    (RawCandidateSerializedInputWordHeaders.headers_safe q full state hf (input_count_le hinput))
  have hd := headers_ready q full containing start hbound hcode state hinput hpc ha
  let copied := natRun rom containing (89 * (full.length * q) + 49) headed
  have cs := copy_raw_safe q full containing start hbound hcode headed hd.1 hs.2 hend
  have cd := RawCandidateSerializedRawCopy.copy_raw q full containing start hbound hcode headed hd.1
  have rawWritten := RawCandidateSerializedInputRun.raw_prefix_written q full copied cd.1.stage.headers cd.2.1
  let initialized := natRun rom containing 16 copied
  have ini := node_init_safe q full containing start hbound hcode copied cd.1.stage cs.2
  have idata := RawCandidateSerializedInputRun.node_init q full containing start hbound hcode copied cd.1.stage rawWritten
  let ord := fun node => initialized.heap (ordAddress full.length q node)
  let count := (prepareNormalization q full).indexed.nodes.size
  let nodeSteps := nodeScanSteps full.length q ord count + 20
  let steps := 79 + ((89 * (full.length * q) + 49) + (16 + nodeSteps))
  let finished := natRun rom containing nodeSteps initialized
  have scan := node_scan_safe q full containing start hbound hcode initialized idata.1 ini.2.1 hend
  have sd := RawCandidateSerializedInputRun.node_scan q full containing start hbound hcode initialized idata.1 idata.2.1
  have hsteps : steps ≤ 256 * (full.length * q + count * q + count + 1) := by
    have hn := RawCandidateSerializedInputRun.nodeScanSteps_le full.length q ord count
    dsimp only [steps, nodeSteps]
    nlinarith
  have hrun : natRun rom containing steps state = finished := by
    dsimp only [steps]
    rw [natRun_add]
    change natRun rom containing ((89 * (full.length * q) + 49) + (16 + nodeSteps)) headed = _
    rw [natRun_add]
    change natRun rom containing (16 + nodeSteps) copied = _
    rw [natRun_add]
  have headFrame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state headed :=
    aboveFrame_mono _ _ 6 _ (by unfold RawCandidateSerializedInputLayout.prefixLength; omega) hd.2
  have copyFrame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) headed copied :=
    aboveFrame_mono _ _ (6 + full.length * q) _ (by unfold RawCandidateSerializedInputLayout.prefixLength; omega) cd.2.2
  have frame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state finished :=
    AboveFrame.trans _ _ _ headFrame (AboveFrame.trans _ _ _ copyFrame (AboveFrame.trans _ _ _ idata.2.2 sd.2.2))
  dsimp only [chunkLength] at hs
  have afterInit : PrefixSafe (SafePoint q full containing start) rom containing copied (16 + nodeSteps) :=
    PrefixSafe.add _ _ _ _ _ _ ini.1 scan.1
  have afterHead : PrefixSafe (SafePoint q full containing start) rom containing headed ((89 * (full.length * q) + 49) + (16 + nodeSteps)) :=
    PrefixSafe.add _ _ _ _ _ _ cs.1 afterInit
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state steps :=
    PrefixSafe.add _ _ _ _ _ _ hs.1 afterHead
  refine ⟨steps, hsteps, ?_⟩
  dsimp only
  rw [hrun]
  exact ⟨allSafe, scan.2.1, sd.1, sd.2.1, frame⟩

theorem materialize_serialized_prefix_nat_safe (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) containing steps state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state steps ∧
      RegistersFit (indexWidth 16 full.length q) result ∧ StageReady q full (5 * (start + 443)) result ∧
      (∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
        result.heap position = (serializeROM (givenTreeROM q full)).getD position 0) ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  obtain ⟨steps, bound, safe, fits, ready, written, frame⟩ :=
    materialize_prefix_nat_safe q full containing start hbound hcode state hinput hpc ha hf hend
  refine ⟨steps, bound, safe, fits, ready, ?_, frame⟩
  intro position hp
  have h := written position hp
  rw [RawCandidateSerializedInputLayout.prefixWords_eq_serialize_take q full hq hlaminar] at h
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp] using h

omit hbound hcode in
theorem word_run_eq_nat_of_prefixSafe (state : NatState) (steps : Nat)
    (safe : PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state steps)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    packingRun (rawIncidenceROM q full) containing steps (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing steps state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ steps hwords
  intro k hk
  have point := safe k hk
  exact ⟨point.1, point.pcFits hend⟩

theorem materialize_serialized_prefix_word (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) containing steps state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state steps ∧
      RegistersFit (indexWidth 16 full.length q) result ∧
      packingRun (rawIncidenceROM q full) containing steps (state.toWord (indexWidth 16 full.length q)) =
        result.toWord (indexWidth 16 full.length q) ∧ StageReady q full (5 * (start + 443)) result ∧
      (∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
        result.heap position = (serializeROM (givenTreeROM q full)).getD position 0) ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  obtain ⟨steps, bound, safe, fits, ready, written, frame⟩ :=
    materialize_serialized_prefix_nat_safe q full containing start hbound hcode state hinput hpc ha hf hend hq hlaminar
  exact ⟨steps, bound, safe, fits, word_run_eq_nat_of_prefixSafe q full containing start state steps safe hend hwords,
    ready, written, frame⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWord
