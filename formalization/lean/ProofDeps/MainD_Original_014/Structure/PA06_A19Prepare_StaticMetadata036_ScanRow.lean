module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanIteration

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual row initialization and complete inner scan. The invariant tracks
all earlier leaf/tool values, so matched local writes are lifted to coverage
of every tool, rather than being counted as complete by themselves. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel)

def rowInitHeap (q : Nat) (full : List (Finset (Fin q))) (CB P node card : Nat) (heap : Nat → Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update heap
    (fieldAddress P full.length (preparedSize q full) .leaf node) 0) (CB + 21) card) (CB + 20) 0

theorem rowInit_frame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (card : Nat) (before after : NatState)
    (hh : after.heap = rowInitHeap q full CB P node.val card before.heap) : ScanFrame q full CB P before after := by
  intro address hn
  have h20 : address ≠ CB + 20 := by unfold ScanAllowed at hn; omega
  have h21 : address ≠ CB + 21 := by unfold ScanAllowed at hn; omega
  have hleaf : address ≠ fieldAddress P full.length (preparedSize q full) .leaf node.val := by
    have hb : node.val < preparedSize q full := node.isLt
    unfold ScanAllowed fieldAddress fieldFactor fieldExtra at *
    omega
  rw [hh]
  simp [rowInitHeap, h20, h21, hleaf]

theorem scanRowInitialize_effect (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (state : NatState)
    (input : ScanInput q full CB P state) (hnode : state.heap (CB + 19) = node.val)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full)) :
    let after := runOps (rawIncidenceROM q full) scanRowInitialize state
    after.register .address = CB ∧ after.heap = rowInitHeap q full CB P node.val
      ((prepareNormalization q full).indexed.metadata.cardinalities.get node) state.heap := by
  obtain ⟨candidate, hord, hsupport⟩ := input.raw.ordered node
  have hcard : state.heap (rawCardAddress CB candidate.val) =
      (prepareNormalization q full).indexed.metadata.cardinalities.get node := by
    rw [input.raw.cards candidate, metadata_cardinality]
    exact congrArg Finset.card hsupport
  have below := scan_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have hleaf : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  simp (disch := omega) [scanRowInitialize, loadRel, storeRel, setRel, storeField,
    fieldPointer, fieldPointerLead, fieldPointerExtra, cardProgram, fieldFactor, fieldExtra, fieldAddress,
    rowInitHeap, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    input.address, input.base, input.nodes, input.raw.mass_cell, hnode,
    rawOrdAddress, rawCardAddress, Function.update_apply,
    Nat.mul_comm, Nat.add_comm, Nat.add_left_comm] at hord hcard hleaf ⊢
  have cardKey : CB + 532 + candidate.val = CB + (candidate.val + 532) := by omega
  have leafKey : node.val + (2 + (P + 4 + 5 * preparedSize q full)) =
      node.val + (P + 6 + 5 * preparedSize q full) := by omega
  rw [hord, cardKey, hcard, leafKey]

theorem row_init_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (node : (prepareNormalization q full).indexed.NodeId) (pointer nextPointer : Nat)
    (before after : NatState) (ready : LeafOuterReady q full CB P node.val pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = rowInitHeap q full CB P node.val
      ((prepareNormalization q full).indexed.metadata.cardinalities.get node) before.heap)
    (hCB : after.register .address = CB) (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    LeafInnerReady q full CB P reference node 0 nextPointer after ∧ ScanFrame q full CB P before after := by
  have frame := rowInit_frame q full CB P node _ before after hh
  have below := scan_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have hleaf : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_frame ready.input hlayout frame hCB
  · rw [hh]
    simp (disch := omega) [rowInitHeap, ready.node_cell]
  · rw [hh]
    simp only [rowInitHeap, Function.update_self]
  · rw [hh]
    simp (disch := omega) [rowInitHeap]
  · rw [hh]
    simp (disch := omega) [rowInitHeap, scanWinner]
  · intro earlier he
    have he' : earlier.val < preparedSize q full := earlier.isLt
    have ha' : fieldAddress P full.length (preparedSize q full) .leaf earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    rw [hh]
    simpa (disch := omega) [rowInitHeap, Function.update_apply, fieldAddress, fieldFactor, fieldExtra]
      using ready.leaves earlier he
  · intro tool he
    have ht := tool.isLt
    have ha' : fieldAddress P full.length (preparedSize q full) .tool tool.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hc := leaf_address_lt_tool P full.length (preparedSize q full) node.val tool.val hn
    rw [hh]
    simpa (disch := omega) [rowInitHeap, Function.update_apply] using ready.tools tool he
  · intro tool ht _
    omega
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)

include referenceData hlayout code

theorem leaf_inner_scan_partial (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafInnerReady q full CB P reference node 0 (5 * (start + 51)) before)
    (count : Nat) (hc : count ≤ q) :
    ∃ clock ≤ 116 * count,
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafInnerReady q full CB P reference node count (5 * (start + 51)) after ∧
        ScanFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨0, by omega, ready, ScanFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, hp, previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing previousClock before
    obtain ⟨nextClock, hn, nextReady, nextFrame⟩ := leaf_pair_iteration q full CB P reference referenceData
      hlayout containing start code node ⟨count, by omega⟩ previous previousReady
    refine ⟨previousClock + nextClock, by omega, ?_⟩
    rw [natRun_add]
    exact ⟨nextReady, previousFrame.trans nextFrame⟩

omit referenceData in
theorem leaf_row_initialize (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafOuterReady q full CB P node.val (5 * (start + 4)) before) :
    let after := natRun (rawIncidenceROM q full) containing 47 before
    LeafInnerReady q full CB P reference node 0 (5 * (start + 51)) after ∧
      ScanFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have hp : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) node.val 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, ite_eq_right (by have hn : node.val < preparedSize q full := node.isLt; omega), ready.pc]
    omega
  have ha : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  let after := runOps rom scanRowInitialize tested
  have testedInput : ScanInput q full CB P tested :=
    ScanInput.of_frame ready.input hlayout (fun _ _ => rfl) ready.input.address
  have effect := scanRowInitialize_effect q full CB P node tested testedInput ready.node_cell hlayout
  have hpc : after.pc = 5 * (start + 51) := by
    rw [runOps_pc rom _ tested (by
      simp [scanRowInitialize, loadRel, storeRel, setRel, storeField, fieldPointer,
        fieldPointerLead, fieldPointerExtra, cardProgram, NoJump]), hp,
      show scanRowInitialize.length = 38 from rfl]
    omega
  have hstate := row_init_ready q full CB P reference node (5 * (start + 4)) (5 * (start + 51))
    before after ready hlayout effect.2 effect.1 hpc ((runOps_halted rom _ tested).trans ha)
  have testRun : natRun rom containing 9 before = tested :=
    scan_chunk_run rom containing start code .outerTest before ready.pc ready.active
  have rowRun : natRun rom containing 38 tested = after :=
    scan_chunk_run rom containing start code .rowInitialize tested hp ha
  have finalRun : natRun (rawIncidenceROM q full) containing 47 before = after := by
    change natRun rom containing (9 + 38) before = after
    exact (natRun_add rom containing 9 38 before).trans
      ((congrArg (natRun rom containing 38) testRun).trans rowRun)
  rw [finalRun]
  exact hstate

end Actual
end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
