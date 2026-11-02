module

public import PaperProofs.Structure.RawCandidateSerializedReady
public import PaperProofs.Structure.RawCandidateSerializedRawCopy

/-! Actual node/tool loops and final assembly of the serialized input
prefix.  The raw-copy phase is linked through its separate machine proof. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputRun

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedInputRAM RawCandidateSerializedReady
open RawCandidateWorkspaceInit (workspaceBase candidateCount)

def nodeDestination (q : Nat) (full : List (Finset (Fin q))) (node tool : Nat) : Nat :=
  6 + full.length * q + node * q + tool

def PrefixWritten (q : Nat) (full : List (Finset (Fin q))) (upto : Nat) (state : NatState) : Prop :=
  ∀ position < upto, state.heap position = (RawCandidateSerializedInputLayout.prefixWords q full).getD position 0

theorem nodeDestination_lt_prefix (q : Nat) (full : List (Finset (Fin q))) (node tool : Nat)
    (hn : node < (prepareNormalization q full).indexed.nodes.size) (ht : tool < q) :
    nodeDestination q full node tool < RawCandidateSerializedInputLayout.prefixLength q full := by
  have hrow := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at hrow
  unfold nodeDestination RawCandidateSerializedInputLayout.prefixLength
  omega

theorem nodeDestination_le_prefix (q : Nat) (full : List (Finset (Fin q))) (node tool : Nat)
    (hn : node < (prepareNormalization q full).indexed.nodes.size) (ht : tool ≤ q) :
    nodeDestination q full node tool ≤ RawCandidateSerializedInputLayout.prefixLength q full := by
  have hrow := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at hrow
  unfold nodeDestination RawCandidateSerializedInputLayout.prefixLength
  omega

theorem nodeDestination_next_row (q : Nat) (full : List (Finset (Fin q))) (node : Nat) :
    nodeDestination q full node q = nodeDestination q full (node + 1) 0 := by
  simp only [nodeDestination, Nat.add_mul, Nat.one_mul, Nat.add_zero]
  omega

theorem PrefixWritten.succ (q : Nat) (full : List (Finset (Fin q))) (upto : Nat)
    {before after : NatState} (hp : PrefixWritten q full upto before)
    (hword : after.heap upto = (RawCandidateSerializedInputLayout.prefixWords q full).getD upto 0)
    (hframe : ∀ position < upto, after.heap position = before.heap position) :
    PrefixWritten q full (upto + 1) after := by
  intro position hi
  by_cases heq : position = upto
  · simpa only [heq] using hword
  · have hless : position < upto := by omega
    exact (hframe position hless).trans (hp position hless)

theorem PrefixWritten.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {upto : Nat}
    {before after : NatState} (hp : PrefixWritten q full upto before) (hh : after.heap = before.heap) :
    PrefixWritten q full upto after := fun position hi => (congrFun hh position).trans (hp position hi)

theorem raw_prefix_written (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hh : HeaderSpec q full state)
    (hraw : ∀ offset < full.length * q, state.heap (6 + offset) = (incidence full).getD offset 0) :
    PrefixWritten q full (6 + full.length * q) state := by
  intro position hp
  by_cases hsmall : position < 6
  · exact hh.prefix position hsmall
  · have hoff : position = 6 + (position - 6) := by omega
    rw [hoff, hraw (position - 6) (by omega), RawCandidateSerializedInputLayout.prefixWords_getD_raw
      q full (position - 6) (by omega)]

theorem prepared_order_getD_eq_decode (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).order.getD node.val ∅ = (prepareNormalization q full).indexed.decode node := by
  have hn : node.val < (prepareNormalization q full).order.length := by
    have h : node.val < (prepareNormalization q full).order.toArray.size := node.isLt
    simpa only [List.size_toArray] using h
  rw [List.getD_eq_getElem _ _ hn]
  rfl

theorem tool_heap_ready (q : Nat) (full : List (Finset (Fin q)))
    (node tool pointer nextPointer word : Nat) {before after : NatState}
    (ready : ToolReady q full node tool pointer before)
    (hn : node < (prepareNormalization q full).indexed.nodes.size) (ht : tool < q)
    (hh : after.heap = Function.update
      (Function.update before.heap (nodeDestination q full node tool) word)
      (workspaceBase full.length q + 2) (tool + 1))
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    ToolReady q full node (tool + 1) nextPointer after ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after ∧
      (∀ position < nodeDestination q full node tool, after.heap position = before.heap position) := by
  have hb := RawCandidateWorkspaceInit.workspaceBase_ge full.length q
  have hprefix : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q :=
    prefixLength_lt_base q full
  have hdest := nodeDestination_lt_prefix q full node tool hn ht
  have hdb : nodeDestination q full node tool < workspaceBase full.length q := hdest.trans hprefix
  have hf : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after := by
    intro address hbound _h1 h2 _h3
    rw [hh]
    simp [h2, show address ≠ nodeDestination q full node tool by omega]
  refine ⟨?_, hf, ?_⟩
  · constructor
    · constructor
      · intro position hposition
        rw [hh]
        simpa (disch := omega) [nodeDestination] using ready.stage.headers position hposition
      · exact InputSpec.of_aboveFrame q full _ ready.stage.input hprefix.le hf
      · rw [hh]
        simpa (disch := omega) using ready.stage.raw_count
      · exact hp
      · exact ha
    · rw [hh]
      simpa (disch := omega) using ready.node_cell
    · rw [hh]
      simp
  · intro position hposition
    rw [hh]
    simp [show position ≠ workspaceBase full.length q + 2 by omega,
      show position ≠ nodeDestination q full node tool by omega]

theorem control_update_ready (q : Nat) (full : List (Finset (Fin q)))
    (pointer nextPointer offset value : Nat) {before after : NatState}
    (ready : StageReady q full pointer before) (hoffset : offset = 1 ∨ offset = 2)
    (hh : after.heap = Function.update before.heap (workspaceBase full.length q + offset) value)
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    StageReady q full nextPointer after ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after ∧
      (∀ position < workspaceBase full.length q, after.heap position = before.heap position) := by
  have hb := RawCandidateWorkspaceInit.workspaceBase_ge full.length q
  have hprefix : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
  have hf : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after := by
    intro address _hbound h1 h2 _h3
    rw [hh]
    rcases hoffset with rfl | rfl
    · exact Function.update_of_ne h1 _ _
    · exact Function.update_of_ne h2 _ _
  have hbelow : ∀ position < workspaceBase full.length q, after.heap position = before.heap position := by
    intro position hposition
    rw [hh]
    simp (disch := omega)
  refine ⟨?_, hf, hbelow⟩
  constructor
  · intro position hposition
    exact (hbelow position (by omega)).trans (ready.headers position hposition)
  · exact InputSpec.of_aboveFrame q full _ ready.input hprefix.le hf
  · rw [hh]
    rcases hoffset with rfl | rfl <;> simpa using ready.raw_count
  · exact hp
  · exact ha

def nodeBitSteps (N candidate tool : Nat) : Nat :=
  140 + (RawCandidateIncidenceRAM.querySteps N candidate tool - 1)

theorem nodeBitSteps_le (N candidate tool : Nat) : nodeBitSteps N candidate tool ≤ 161 := by
  have h := RawCandidateIncidenceRAM.querySteps_le N candidate tool
  unfold nodeBitSteps
  omega

def toolScanSteps (N candidate count : Nat) : Nat :=
  ∑ tool ∈ Finset.range count, nodeBitSteps N candidate tool

theorem toolScanSteps_succ (N candidate count : Nat) :
    toolScanSteps N candidate (count + 1) = toolScanSteps N candidate count + nodeBitSteps N candidate count :=
  Finset.sum_range_succ _ _

theorem toolScanSteps_le (N candidate count : Nat) : toolScanSteps N candidate count ≤ 161 * count := by
  calc
    _ ≤ ∑ _tool ∈ Finset.range count, 161 := Finset.sum_le_sum (fun tool _ => nodeBitSteps_le N candidate tool)
    _ = _ := by simp [Nat.mul_comm]

def rowSteps (N q candidate : Nat) : Nat := 91 + toolScanSteps N candidate q

theorem rowSteps_le (N q candidate : Nat) : rowSteps N q candidate ≤ 161 * q + 91 := by
  have h := toolScanSteps_le N candidate q
  unfold rowSteps
  omega

def nodeScanSteps (N q : Nat) (ord : Nat → Nat) (count : Nat) : Nat :=
  ∑ node ∈ Finset.range count, rowSteps N q (ord node)

theorem nodeScanSteps_succ (N q : Nat) (ord : Nat → Nat) (count : Nat) :
    nodeScanSteps N q ord (count + 1) = nodeScanSteps N q ord count + rowSteps N q (ord count) :=
  Finset.sum_range_succ _ _

theorem nodeScanSteps_le (N q : Nat) (ord : Nat → Nat) (count : Nat) :
    nodeScanSteps N q ord count ≤ count * (161 * q + 91) := by
  calc
    _ ≤ ∑ _node ∈ Finset.range count, (161 * q + 91) :=
      Finset.sum_le_sum (fun node _ => rowSteps_le N q (ord node))
    _ = _ := by simp [Nat.mul_comm]

private theorem ord_preserved (q : Nat) (full : List (Finset (Fin q))) (node : Nat)
    {before after : NatState}
    (h : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) before after) :
    after.heap (ordAddress full.length q node) = before.heap (ordAddress full.length q node) := by
  have hb : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
  exact h _ (by unfold ordAddress; omega) (by unfold ordAddress; omega)
    (by unfold ordAddress; omega) (by unfold ordAddress; omega)

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 443 ≤ containing.length)
  (hcode : ∀ position < 443, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem node_init (state : NatState) (ready : StageReady q full (5 * (start + 184)) state)
    (hwritten : PrefixWritten q full (6 + full.length * q) state) :
    let result := natRun (rawIncidenceROM q full) containing 16 state
    NodeReady q full 0 (5 * (start + 200)) result ∧
      PrefixWritten q full (nodeDestination q full 0 0) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let initialized := runOps (rawIncidenceROM q full) (setCache 1 0) state
  have hh : initialized.heap = Function.update state.heap (workspaceBase full.length q + 1) 0 := setCache_heap q full 1 0 state
  have hp : initialized.pc = 5 * (start + 200) := by
    rw [show initialized = runOps _ _ _ from rfl,
      runOps_pc _ _ _ (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]),
      setCache_length, ready.pc]
    omega
  have ha : initialized.halted = false := (runOps_halted _ _ _).trans ready.active
  have hr := control_update_ready q full (5 * (start + 184)) (5 * (start + 200)) 1 0 ready
    (Or.inl rfl) hh hp ha
  rw [run_nodeInit _ containing start hbound hcode state ready.pc ready.active]
  refine ⟨⟨hr.1, ?_⟩, ?_, hr.2.1⟩
  · rw [hh]
    simp
  · intro position hposition
    have hprefix : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
    have hpos : position < 6 + full.length * q := by simpa only [nodeDestination, Nat.zero_mul, Nat.add_zero] using hposition
    exact (hr.2.2 position (by unfold RawCandidateSerializedInputLayout.prefixLength at hprefix; omega)).trans
      (hwritten position hpos)

theorem tool_init (node : Nat) (state : NatState)
    (ready : NodeReady q full node (5 * (start + 220)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hwritten : PrefixWritten q full (nodeDestination q full node 0) state) :
    let result := natRun (rawIncidenceROM q full) containing 16 state
    ToolReady q full node 0 (5 * (start + 236)) result ∧
      PrefixWritten q full (nodeDestination q full node 0) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let initialized := runOps (rawIncidenceROM q full) (setCache 2 0) state
  have hh : initialized.heap = Function.update state.heap (workspaceBase full.length q + 2) 0 := setCache_heap q full 2 0 state
  have hp : initialized.pc = 5 * (start + 236) := by
    rw [show initialized = runOps _ _ _ from rfl,
      runOps_pc _ _ _ (by simp [setCache, storeCache, RawCandidateWorkspaceBaseRAM.program, NoJump]),
      setCache_length, ready.stage.pc]
    omega
  have ha : initialized.halted = false := (runOps_halted _ _ _).trans ready.stage.active
  have hr := control_update_ready q full (5 * (start + 220)) (5 * (start + 236)) 2 0 ready.stage
    (Or.inr rfl) hh hp ha
  rw [run_toolInit _ containing start hbound hcode state ready.stage.pc ready.stage.active]
  refine ⟨⟨hr.1, ?_, ?_⟩, ?_, hr.2.1⟩
  · rw [hh]
    simpa using ready.node_cell
  · rw [hh]
    simp
  · intro position hposition
    have hprefix : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
    have hdest := nodeDestination_le_prefix q full node 0 hn (Nat.zero_le _)
    exact (hr.2.2 position (by omega)).trans (hwritten position hposition)

theorem node_bit_iteration (node tool : Nat) (state : NatState)
    (ready : ToolReady q full node tool (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size) (ht : tool < q)
    (hwritten : PrefixWritten q full (nodeDestination q full node tool) state) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (nodeBitSteps full.length candidate tool) state
    ToolReady q full node (tool + 1) (5 * (start + 236)) result ∧
      PrefixWritten q full (nodeDestination q full node tool + 1) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let candidate := state.heap (ordAddress full.length q node)
  have hc : candidate < full.length + q + 1 := ready.stage.input.ord_legal node hn
  let tested := runOps rom (boundedTest 2 4 (start + 408)) state
  have htest := boundedTest_values q full 2 4 (start + 408) state
  dsimp only at htest
  have hth : tested.heap = state.heap := htest.1
  have htq : state.heap 4 = q := ready.stage.headers.tools
  have htestpc : tested.pc = 5 * (start + 256) := by
    have h := htest.2.1
    rw [htq, ready.tool_cell, ite_eq_right (Nat.sub_ne_zero_of_lt ht), ready.stage.pc] at h
    dsimp only [tested]
    omega
  have htestactive : tested.halted = false := htest.2.2.trans ready.stage.active
  let args := runOps rom arguments tested
  have hargs := arguments_values q full tested
  dsimp only at hargs
  have hargold : args.register .old = candidate := by
    simpa only [hth, ready.node_cell] using hargs.1
  have hargfresh : args.register .fresh = tool := by
    have h : args.register .fresh = state.heap (workspaceBase full.length q + 2) := by
      simpa only [hth] using hargs.2.1
    exact h.trans ready.tool_cell
  have hargh : args.heap = state.heap := hargs.2.2.1.trans hth
  have hargpc : args.pc = 5 * (start + 305) := by
    have h := hargs.2.2.2.1
    rw [htestpc] at h
    dsimp only [args]
    omega
  have hargactive : args.halted = false := hargs.2.2.2.2.trans htestactive
  let querySteps := RawCandidateIncidenceRAM.querySteps full.length candidate tool - 1
  let queried := natRun rom containing querySteps args
  have hs := query_call q full containing start hbound hcode ⟨candidate, hc⟩ ⟨tool, ht⟩ args
    hargpc hargactive hargold hargfresh
  rcases hs with ⟨hv, _, hsfresh, hsh, hsp, hsa⟩
  have hqh : queried.heap = state.heap := hsh.trans hargh
  have hqfresh : queried.register .fresh = tool := hsfresh.trans hargfresh
  have hqnode : queried.heap (workspaceBase full.length q + 1) = node := (congrFun hqh _).trans ready.node_cell
  have hqtool : queried.heap (workspaceBase full.length q + 2) = tool := (congrFun hqh _).trans ready.tool_cell
  have hqraw : queried.heap (workspaceBase full.length q + 3) = full.length * q := (congrFun hqh _).trans ready.stage.raw_count
  have hdecode : (RawCandidateOrder.candidateSupports q full).getD candidate ∅ =
      (prepareNormalization q full).indexed.decode ⟨node, hn⟩ :=
    (ready.stage.input.ord_support node hn).trans (prepared_order_getD_eq_decode q full ⟨node, hn⟩)
  have hbit : bit (decide ((⟨tool, ht⟩ : Fin q) ∈ (RawCandidateOrder.candidateSupports q full).getD candidate ∅)) =
      (RawCandidateSerializedInputLayout.prefixWords q full).getD (nodeDestination q full node tool) 0 := by
    rw [hdecode]
    exact (RawCandidateSerializedInputLayout.prefixWords_getD_node_bit q full ⟨node, hn⟩ ⟨tool, ht⟩).symm
  have hqword : queried.register .value =
      (RawCandidateSerializedInputLayout.prefixWords q full).getD (nodeDestination q full node tool) 0 := hv.trans hbit
  have hdest := nodeDestination_lt_prefix q full node tool hn ht
  have hprefix : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
  have hsep : 6 + queried.heap (workspaceBase full.length q + 3) +
      queried.heap (workspaceBase full.length q + 1) * q + queried.register .fresh < workspaceBase full.length q := by
    rw [hqraw, hqnode, hqfresh]
    exact hdest.trans hprefix
  let finished := runOps rom (toolTail start) queried
  have htail := toolTail_values q full start queried hsep
  dsimp only at htail
  have hfh : finished.heap = Function.update
      (Function.update state.heap (nodeDestination q full node tool)
        ((RawCandidateSerializedInputLayout.prefixWords q full).getD (nodeDestination q full node tool) 0))
      (workspaceBase full.length q + 2) (tool + 1) := by
    have h := htail.1
    rw [hqraw, hqnode, hqfresh, hqtool, hqword, hqh] at h
    exact h
  have hquerypc : queried.pc = 5 * (start + 337) := by simpa only [Nat.add_assoc] using hsp
  have hrun : natRun rom containing (nodeBitSteps full.length candidate tool) state = finished := by
    rw [show nodeBitSteps full.length candidate tool = 20 + (49 + (querySteps + 71)) by
      unfold nodeBitSteps; dsimp only [querySteps]; omega,
      natRun_add, run_toolTest rom containing start hbound hcode state ready.stage.pc ready.stage.active]
    change natRun rom containing (49 + (querySteps + 71)) tested = _
    rw [natRun_add, run_arguments rom containing start hbound hcode tested htestpc htestactive, natRun_add]
    exact run_toolTail rom containing start hbound hcode queried hquerypc hsa
  have hready := tool_heap_ready q full node tool (5 * (start + 236)) (5 * (start + 236))
    _ ready hn ht hfh htail.2.1 (htail.2.2.trans hsa)
  have hw : PrefixWritten q full (nodeDestination q full node tool + 1) finished := by
    apply PrefixWritten.succ q full _ hwritten ?_ hready.2.2
    rw [hfh]
    simp (disch := omega)
  dsimp only
  rw [hrun]
  exact ⟨hready.1, hw, hready.2.1⟩

theorem tool_scan_partial (node : Nat) (state : NatState)
    (ready : ToolReady q full node 0 (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hwritten : PrefixWritten q full (nodeDestination q full node 0) state)
    (count : Nat) (hcount : count ≤ q) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (toolScanSteps full.length candidate count) state
    ToolReady q full node count (5 * (start + 236)) result ∧
      PrefixWritten q full (nodeDestination q full node count) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  revert hcount
  induction count with
  | zero =>
    intro _
    simpa only [toolScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show ToolReady q full node 0 (5 * (start + 236)) state ∧
        PrefixWritten q full (nodeDestination q full node 0) state ∧
        AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state state from
          ⟨ready, hwritten, AboveFrame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hcount
    rcases ih (by omega) with ⟨rp, hwp, hfp⟩
    let previous := natRun (rawIncidenceROM q full) containing
      (toolScanSteps full.length (state.heap (ordAddress full.length q node)) count) state
    have hid : previous.heap (ordAddress full.length q node) = state.heap (ordAddress full.length q node) :=
      ord_preserved q full node hfp
    have hs := node_bit_iteration q full containing start hbound hcode node count previous rp hn (by omega) hwp
    dsimp only at hs
    rw [hid] at hs
    have hrun : natRun (rawIncidenceROM q full) containing
        (toolScanSteps full.length (state.heap (ordAddress full.length q node)) (count + 1)) state =
        natRun (rawIncidenceROM q full) containing
          (nodeBitSteps full.length (state.heap (ordAddress full.length q node)) count) previous := by
      rw [toolScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    refine ⟨hs.1, ?_, AboveFrame.trans _ _ _ hfp hs.2.2⟩
    simpa only [nodeDestination, Nat.add_assoc] using hs.2.1

theorem tool_scan (node : Nat) (state : NatState)
    (ready : ToolReady q full node 0 (5 * (start + 236)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hwritten : PrefixWritten q full (nodeDestination q full node 0) state) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (toolScanSteps full.length candidate q + 20) state
    ToolReady q full node q (5 * (start + 408)) result ∧
      PrefixWritten q full (nodeDestination q full node q) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let previous := natRun (rawIncidenceROM q full) containing
    (toolScanSteps full.length (state.heap (ordAddress full.length q node)) q) state
  rcases tool_scan_partial q full containing start hbound hcode node state ready hn hwritten q le_rfl with
    ⟨rp, hwp, hfp⟩
  have ht := boundedTest_values q full 2 4 (start + 408) previous
  dsimp only at ht
  have hh : (runOps (rawIncidenceROM q full) (boundedTest 2 4 (start + 408)) previous).heap = previous.heap := ht.1
  have hq : previous.heap 4 = q := rp.stage.headers.tools
  have hj : previous.heap (workspaceBase full.length q + 2) = q := rp.tool_cell
  have hp : (runOps (rawIncidenceROM q full) (boundedTest 2 4 (start + 408)) previous).pc = 5 * (start + 408) := by
    simpa only [hq, hj, Nat.sub_self, ite_true] using ht.2.1
  have ha : (runOps (rawIncidenceROM q full) (boundedTest 2 4 (start + 408)) previous).halted = false := ht.2.2.trans rp.stage.active
  have hrun : natRun (rawIncidenceROM q full) containing
      (toolScanSteps full.length (state.heap (ordAddress full.length q node)) q + 20) state =
      runOps (rawIncidenceROM q full) (boundedTest 2 4 (start + 408)) previous := by
    rw [natRun_add]
    exact run_toolTest _ containing start hbound hcode previous rp.stage.pc rp.stage.active
  dsimp only
  rw [hrun]
  refine ⟨⟨StageReady.of_heap_eq rp.stage hh hp ha,
    (congrFun hh _).trans rp.node_cell, (congrFun hh _).trans rp.tool_cell⟩,
    PrefixWritten.of_heap_eq hwp hh, ?_⟩
  intro address hbound' h1 h2 h3
  exact (congrFun hh address).trans (hfp address hbound' h1 h2 h3)

theorem node_iteration (node : Nat) (state : NatState)
    (ready : NodeReady q full node (5 * (start + 200)) state)
    (hn : node < (prepareNormalization q full).indexed.nodes.size)
    (hwritten : PrefixWritten q full (nodeDestination q full node 0) state) :
    let candidate := state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (rowSteps full.length q candidate) state
    NodeReady q full (node + 1) (5 * (start + 200)) result ∧
      PrefixWritten q full (nodeDestination q full (node + 1) 0) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (boundedTest 1 5 (start + 443)) state
  have ht := boundedTest_values q full 1 5 (start + 443) state
  dsimp only at ht
  have hth : tested.heap = state.heap := ht.1
  have hsize : state.heap 5 = (prepareNormalization q full).indexed.nodes.size := ready.stage.headers.count
  have htp : tested.pc = 5 * (start + 220) := by
    have h := ht.2.1
    rw [hsize, ready.node_cell, ite_eq_right (Nat.sub_ne_zero_of_lt hn), ready.stage.pc] at h
    dsimp only [tested]
    omega
  have hta : tested.halted = false := ht.2.2.trans ready.stage.active
  have rt : NodeReady q full node (5 * (start + 220)) tested :=
    ⟨StageReady.of_heap_eq ready.stage hth htp hta, (congrFun hth _).trans ready.node_cell⟩
  let initialized := natRun rom containing 16 tested
  rcases tool_init q full containing start hbound hcode node tested rt hn
    (PrefixWritten.of_heap_eq hwritten hth) with ⟨ri, hwi, hfi⟩
  have hid : initialized.heap (ordAddress full.length q node) = state.heap (ordAddress full.length q node) :=
    (ord_preserved q full node hfi).trans (congrFun hth _)
  let scanned := natRun rom containing
    (toolScanSteps full.length (state.heap (ordAddress full.length q node)) q + 20) initialized
  have hs := tool_scan q full containing start hbound hcode node initialized ri hn hwi
  dsimp only at hs
  rw [hid] at hs
  rcases hs with ⟨rs, hws, hfs⟩
  let finished := runOps rom (rowTail start) scanned
  have hr := rowTail_values q full start scanned
  dsimp only at hr
  have hnode : scanned.heap (workspaceBase full.length q + 1) = node := rs.node_cell
  have hfh : finished.heap = Function.update scanned.heap (workspaceBase full.length q + 1) (node + 1) := by
    simpa only [hnode] using hr.1
  have hready := control_update_ready q full (5 * (start + 408)) (5 * (start + 200)) 1 (node + 1)
    rs.stage (Or.inl rfl) hfh hr.2.1 (hr.2.2.trans rs.stage.active)
  have htestframe : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state tested :=
    fun address _ _ _ _ => congrFun hth address
  have hframe := AboveFrame.trans _ _ _ htestframe (AboveFrame.trans _ _ _ hfi (AboveFrame.trans _ _ _ hfs hready.2.1))
  have hrun : natRun rom containing
      (rowSteps full.length q (state.heap (ordAddress full.length q node))) state = finished := by
    rw [show rowSteps full.length q (state.heap (ordAddress full.length q node)) =
        20 + (16 + ((toolScanSteps full.length (state.heap (ordAddress full.length q node)) q + 20) + 35)) by
          unfold rowSteps; omega,
      natRun_add, run_nodeTest rom containing start hbound hcode state ready.stage.pc ready.stage.active]
    change natRun rom containing
      (16 + ((toolScanSteps full.length (state.heap (ordAddress full.length q node)) q + 20) + 35)) tested = _
    rw [natRun_add]
    change natRun rom containing
      ((toolScanSteps full.length (state.heap (ordAddress full.length q node)) q + 20) + 35) initialized = _
    rw [natRun_add]
    exact run_rowTail rom containing start hbound hcode scanned rs.stage.pc rs.stage.active
  dsimp only
  rw [hrun]
  refine ⟨⟨hready.1, ?_⟩, ?_, hframe⟩
  · rw [hfh]
    simp
  · rw [← nodeDestination_next_row q full node]
    intro position hp
    have hdest := nodeDestination_le_prefix q full node q hn le_rfl
    have hb : RawCandidateSerializedInputLayout.prefixLength q full < workspaceBase full.length q := prefixLength_lt_base q full
    exact (hready.2.2 position (by omega)).trans (hws position hp)

theorem node_scan_partial (state : NatState)
    (ready : NodeReady q full 0 (5 * (start + 200)) state)
    (hwritten : PrefixWritten q full (nodeDestination q full 0 0) state)
    (count : Nat) (hcount : count ≤ (prepareNormalization q full).indexed.nodes.size) :
    let ord := fun node => state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing (nodeScanSteps full.length q ord count) state
    NodeReady q full count (5 * (start + 200)) result ∧
      PrefixWritten q full (nodeDestination q full count 0) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  revert hcount
  induction count with
  | zero =>
    intro _
    simpa only [nodeScanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show NodeReady q full 0 (5 * (start + 200)) state ∧ PrefixWritten q full (nodeDestination q full 0 0) state ∧
        AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state state from
          ⟨ready, hwritten, AboveFrame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hcount
    rcases ih (by omega) with ⟨rp, hwp, hfp⟩
    let previous := natRun (rawIncidenceROM q full) containing
      (nodeScanSteps full.length q (fun node => state.heap (ordAddress full.length q node)) count) state
    have hid : previous.heap (ordAddress full.length q count) = state.heap (ordAddress full.length q count) :=
      ord_preserved q full count hfp
    have hs := node_iteration q full containing start hbound hcode count previous rp (by omega) hwp
    dsimp only at hs
    rw [hid] at hs
    have hrun : natRun (rawIncidenceROM q full) containing
        (nodeScanSteps full.length q (fun node => state.heap (ordAddress full.length q node)) (count + 1)) state =
        natRun (rawIncidenceROM q full) containing
          (rowSteps full.length q (state.heap (ordAddress full.length q count))) previous := by
      rw [nodeScanSteps_succ, natRun_add]
    dsimp only
    rw [hrun]
    exact ⟨hs.1, hs.2.1, AboveFrame.trans _ _ _ hfp hs.2.2⟩

theorem node_scan (state : NatState)
    (ready : NodeReady q full 0 (5 * (start + 200)) state)
    (hwritten : PrefixWritten q full (nodeDestination q full 0 0) state) :
    let ord := fun node => state.heap (ordAddress full.length q node)
    let result := natRun (rawIncidenceROM q full) containing
      (nodeScanSteps full.length q ord (prepareNormalization q full).indexed.nodes.size + 20) state
    StageReady q full (5 * (start + 443)) result ∧
      PrefixWritten q full (RawCandidateSerializedInputLayout.prefixLength q full) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let previous := natRun (rawIncidenceROM q full) containing
    (nodeScanSteps full.length q (fun node => state.heap (ordAddress full.length q node))
      (prepareNormalization q full).indexed.nodes.size) state
  rcases node_scan_partial q full containing start hbound hcode state ready hwritten
    (prepareNormalization q full).indexed.nodes.size le_rfl with ⟨rp, hwp, hfp⟩
  have ht := boundedTest_values q full 1 5 (start + 443) previous
  dsimp only at ht
  have hh : (runOps (rawIncidenceROM q full) (boundedTest 1 5 (start + 443)) previous).heap = previous.heap := ht.1
  have hsize : previous.heap 5 = (prepareNormalization q full).indexed.nodes.size := rp.stage.headers.count
  have hnode : previous.heap (workspaceBase full.length q + 1) = (prepareNormalization q full).indexed.nodes.size := rp.node_cell
  have hp : (runOps (rawIncidenceROM q full) (boundedTest 1 5 (start + 443)) previous).pc = 5 * (start + 443) := by
    simpa only [hsize, hnode, Nat.sub_self, ite_true] using ht.2.1
  have ha : (runOps (rawIncidenceROM q full) (boundedTest 1 5 (start + 443)) previous).halted = false := ht.2.2.trans rp.stage.active
  have hrun : natRun (rawIncidenceROM q full) containing
      (nodeScanSteps full.length q (fun node => state.heap (ordAddress full.length q node))
        (prepareNormalization q full).indexed.nodes.size + 20) state =
      runOps (rawIncidenceROM q full) (boundedTest 1 5 (start + 443)) previous := by
    rw [natRun_add]
    exact run_nodeTest _ containing start hbound hcode previous rp.stage.pc rp.stage.active
  dsimp only
  rw [hrun]
  refine ⟨StageReady.of_heap_eq rp.stage hh hp ha, ?_, ?_⟩
  · have h := PrefixWritten.of_heap_eq hwp hh
    simpa only [nodeDestination, Nat.add_zero, RawCandidateSerializedInputLayout.prefixLength] using h
  · intro address hbound' h1 h2 h3
    exact (congrFun hh address).trans (hfp address hbound' h1 h2 h3)

/-- The complete fixed program writes all six headers, all raw bits and
all node bits.  Its only semantic input is the actual cached ID handoff. -/
theorem materialize_prefix (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) containing steps state
    StageReady q full (5 * (start + 443)) result ∧
      PrefixWritten q full (RawCandidateSerializedInputLayout.prefixLength q full) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  let rom := rawIncidenceROM q full
  let headed := natRun rom containing 79 state
  have hh := headers_ready q full containing start hbound hcode state hinput hpc hactive
  dsimp only at hh
  let copied := natRun rom containing (89 * (full.length * q) + 49) headed
  have hc := RawCandidateSerializedRawCopy.copy_raw q full containing start hbound hcode headed hh.1
  dsimp only at hc
  have hwraw : PrefixWritten q full (6 + full.length * q) copied :=
    raw_prefix_written q full copied hc.1.stage.headers hc.2.1
  let initialized := natRun rom containing 16 copied
  have hi := node_init q full containing start hbound hcode copied hc.1.stage hwraw
  dsimp only at hi
  let ord := fun node => initialized.heap (ordAddress full.length q node)
  let count := (prepareNormalization q full).indexed.nodes.size
  let nodeSteps := nodeScanSteps full.length q ord count + 20
  let steps := 79 + ((89 * (full.length * q) + 49) + (16 + nodeSteps))
  let finished := natRun rom containing nodeSteps initialized
  have hs := node_scan q full containing start hbound hcode initialized hi.1 hi.2.1
  dsimp only at hs
  have hclock : steps ≤ 256 * (full.length * q + count * q + count + 1) := by
    have hn := nodeScanSteps_le full.length q ord count
    have hNq := Nat.zero_le (full.length * q)
    have htq := Nat.zero_le (count * q)
    dsimp only [steps, nodeSteps]
    nlinarith
  have hrun : natRun rom containing steps state = finished := by
    dsimp only [steps]
    rw [natRun_add]
    change natRun rom containing ((89 * (full.length * q) + 49) + (16 + nodeSteps)) headed = _
    rw [natRun_add]
    change natRun rom containing (16 + nodeSteps) copied = _
    rw [natRun_add]
  have hheadFrame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state headed :=
    aboveFrame_mono _ _ 6 _ (by unfold RawCandidateSerializedInputLayout.prefixLength; omega) hh.2
  have hrawFrame : AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) headed copied :=
    aboveFrame_mono _ _ (6 + full.length * q) _ (by unfold RawCandidateSerializedInputLayout.prefixLength; omega) hc.2.2
  refine ⟨steps, hclock, ?_⟩
  dsimp only
  rw [hrun]
  exact ⟨hs.1, hs.2.1, AboveFrame.trans _ _ _ hheadFrame
    (AboveFrame.trans _ _ _ hrawFrame (AboveFrame.trans _ _ _ hi.2.2 hs.2.2))⟩

/-- The six computed heads have the original three region lengths on the
positive-q laminar branch.  No internal or child data is manufactured here. -/
theorem materialize_serialized_prefix (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false)
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) containing steps state
    StageReady q full (5 * (start + 443)) result ∧
      (∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
        result.heap position = (serializeROM (givenTreeROM q full)).getD position 0) ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  obtain ⟨steps, hsteps, ready, hwords, hframe⟩ :=
    materialize_prefix q full containing start hbound hcode state hinput hpc hactive
  refine ⟨steps, hsteps, ready, ?_, hframe⟩
  intro position hp
  have h := hwords position hp
  rw [RawCandidateSerializedInputLayout.prefixWords_eq_serialize_take q full hq hlaminar] at h
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hp] using h

end Linked

theorem append_slice (left right : List PackingOp) :
    left.length + 443 ≤ (left ++ programAt left.length ++ right).length ∧
      ∀ position < 443,
        (left ++ programAt left.length ++ right).getD (left.length + position) paddingOp =
          (programAt left.length).getD position paddingOp := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _ (by
      simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega), Nat.add_sub_cancel_left]

theorem materialize_prefix_append (q : Nat) (full : List (Finset (Fin q))) (left right : List PackingOp)
    (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right) steps state
    StageReady q full (5 * (left.length + 443)) result ∧
      PrefixWritten q full (RawCandidateSerializedInputLayout.prefixLength q full) result ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  exact materialize_prefix q full _ left.length (append_slice left right).1 (append_slice left right).2
    state hinput hpc hactive

theorem materialize_serialized_prefix_append (q : Nat) (full : List (Finset (Fin q))) (left right : List PackingOp)
    (state : NatState) (hinput : InputSpec q full state)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false)
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    ∃ steps ≤ 256 * (full.length * q + (prepareNormalization q full).indexed.nodes.size * q +
      (prepareNormalization q full).indexed.nodes.size + 1),
    let result := natRun (rawIncidenceROM q full) (left ++ programAt left.length ++ right) steps state
    StageReady q full (5 * (left.length + 443)) result ∧
      (∀ position < RawCandidateSerializedInputLayout.prefixLength q full,
        result.heap position = (serializeROM (givenTreeROM q full)).getD position 0) ∧
      AboveFrame full.length q (RawCandidateSerializedInputLayout.prefixLength q full) state result := by
  exact materialize_serialized_prefix q full _ left.length (append_slice left right).1 (append_slice left right).2
    state hinput hpc hactive hq hlaminar

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputRun
