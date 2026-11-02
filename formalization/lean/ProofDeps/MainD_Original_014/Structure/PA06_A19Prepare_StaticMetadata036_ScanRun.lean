module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanRow

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete actual Nat node×tool loop, including zero initialization of
internal leaves, all final singleton tool writes and both exhausted guards.
This is the full191-op leaf/tool producer, not just a matched kernel.
Word refinement and the remaining stage producer are separate obligations. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass setRel)

theorem scan_control_frame (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) {offset value : Nat}
    (before after : NatState) (hoffset : offset = 19 ∨ offset = 20 ∨ offset = 21)
    (hh : after.heap = Function.update before.heap (CB + offset) value) : ScanFrame q full CB P before after := by
  intro address hn
  have hne : address ≠ CB + offset := by unfold ScanAllowed at hn; rcases hoffset with h | h | h <;> subst offset <;> omega
  rw [hh, Function.update_of_ne hne]

theorem row_finish_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (reference : NatState) (referenceData : RawCardData q full CB reference)
    (node : (prepareNormalization q full).indexed.NodeId) (pointer nextPointer : Nat)
    (before after : NatState) (ready : LeafInnerReady q full CB P reference node q pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = Function.update before.heap (CB + 19) (node.val + 1))
    (hCB : after.register .address = CB) (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    LeafOuterReady q full CB P (node.val + 1) nextPointer after ∧ ScanFrame q full CB P before after := by
  have frame := scan_control_frame q full CB P before after (Or.inl rfl) hh
  have below := scan_regions_below_control q full CB P hlayout
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_frame ready.input hlayout frame hCB
  · rw [hh, Function.update_self]
  · intro earlier he
    have hn : earlier.val < preparedSize q full := earlier.isLt
    have haddr : fieldAddress P full.length (preparedSize q full) .leaf earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    rw [hh, Function.update_of_ne (by omega)]
    by_cases hprev : earlier.val < node.val
    · exact ready.leaves earlier hprev
    · have heq : earlier = node := Fin.ext (by omega)
      subst earlier
      rw [ready.row_leaf]
      exact leafScan_original q full CB reference referenceData node
  · intro tool ht
    have hn := tool.isLt
    have haddr : fieldAddress P full.length (preparedSize q full) .tool tool.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    rw [hh, Function.update_of_ne (by omega)]
    by_cases hprev : singletonIndex q full tool < node.val
    · exact ready.tools tool hprev
    · have heq : singletonIndex q full tool = node.val := by omega
      rw [heq]
      exact ready.row_tools tool tool.isLt heq
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)

include referenceData hlayout code

theorem leaf_row_finish (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafInnerReady q full CB P reference node q (5 * (start + 51)) before) :
    let after := natRun (rawIncidenceROM q full) containing 20 before
    LeafOuterReady q full CB P (node.val + 1) (5 * (start + 4)) after ∧ ScanFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 180)) before
  have hpc : tested.pc = 5 * (start + 180) := by
    rw [scanBoundedTest_pc rom CB q q 1 20 (start + 180) before
      ready.input.address ready.input.tools ready.tool_cell, Nat.sub_self, ite_eq_left rfl]
  have ha : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  let after := runOps rom (scanOuterTail start) tested
  have tail := scanOuterTail_effect rom CB node.val start tested ready.input.address ready.node_cell
  have next := row_finish_ready q full CB P reference referenceData node (5 * (start + 51)) (5 * (start + 4))
    before after ready hlayout tail.2.1 tail.1 tail.2.2.1 ((tail.2.2.2).trans ha)
  have innerTestRun : natRun rom containing 9 before = tested :=
    scan_chunk_run rom containing start code .innerTest before ready.pc ready.active
  have outerTailRun : natRun rom containing 11 tested = after :=
    scan_chunk_run rom containing start code .outerTail tested hpc ha
  have finalRun : natRun (rawIncidenceROM q full) containing 20 before = after := by
    change natRun rom containing (9 + 11) before = after
    exact (natRun_add rom containing 9 11 before).trans
      ((congrArg (natRun rom containing 11) innerTestRun).trans outerTailRun)
  rw [finalRun]
  exact next

theorem leaf_row_iteration (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafOuterReady q full CB P node.val (5 * (start + 4)) before) :
    ∃ clock ≤ 67 + 116 * q,
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafOuterReady q full CB P (node.val + 1) (5 * (start + 4)) after ∧ ScanFrame q full CB P before after := by
  let initialized := natRun (rawIncidenceROM q full) containing 47 before
  obtain ⟨initReady, initFrame⟩ := leaf_row_initialize q full CB P reference hlayout containing start code node before ready
  obtain ⟨scanClock, hscan, scanReady, scanFrame⟩ := leaf_inner_scan_partial q full CB P reference referenceData
    hlayout containing start code node initialized initReady q le_rfl
  let scanned := natRun (rawIncidenceROM q full) containing scanClock initialized
  have finish := leaf_row_finish q full CB P reference referenceData hlayout containing start code node scanned scanReady
  refine ⟨47 + scanClock + 20, by omega, ?_⟩
  rw [natRun_add, natRun_add]
  exact ⟨finish.1, (initFrame.trans scanFrame).trans finish.2⟩

theorem leaf_outer_scan_partial (before : NatState)
    (ready : LeafOuterReady q full CB P 0 (5 * (start + 4)) before)
    (count : Nat) (hc : count ≤ preparedSize q full) :
    ∃ clock ≤ count * (67 + 116 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafOuterReady q full CB P count (5 * (start + 4)) after ∧ ScanFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨0, by omega, ready, ScanFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, hp, previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing previousClock before
    obtain ⟨nextClock, hn, nextReady, nextFrame⟩ := leaf_row_iteration q full CB P reference referenceData
      hlayout containing start code ⟨count, by change count < preparedSize q full; omega⟩ previous previousReady
    refine ⟨previousClock + nextClock, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · rw [natRun_add]
      exact ⟨nextReady, previousFrame.trans nextFrame⟩

end Actual

/-- Complete true Nat191 producer from arbitrary Nat registers and the real
copied cache/dimensions. Every leaf and every tool has its original value.
No final lookup array or matched-path coverage is an input hypothesis. -/
theorem leaf_tool_build (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (CB P : Nat) (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (before : NatState) (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hpc : before.pc = 5 * start) (ha : before.halted = false) :
    ∃ clock ≤ 13 + preparedSize q full * (67 + 116 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      ScanInput q full CB P after ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        after.heap (fieldAddress P full.length (preparedSize q full) .leaf node.val) = originalLeaf q full node) ∧
      (∀ tool : Fin q,
        after.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) =
          ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val + 1) ∧
      ScanFrame q full CB P before after ∧ after.register .address = CB ∧
      after.pc = 5 * (start + 191) ∧ after.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom scanInitialize before
  have hh : initialized.heap = Function.update before.heap (CB + 19) 0 := by
    simp [initialized, scanInitialize, PA06A19PrepareChildrenCache023.setRel_heap, input.address]
  have hCB : initialized.register .address = CB := input.address
  have frame := scan_control_frame q full CB P before initialized (Or.inl rfl) hh
  have initPC : initialized.pc = 5 * (start + 4) := by
    rw [runOps_pc rom _ before (by simp [scanInitialize, setRel, PA06A19PrepareChildrenCache023.storeRel, NoJump]), hpc,
      show scanInitialize.length = 4 from rfl]
    omega
  have initActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : LeafOuterReady q full CB P 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_frame input hlayout frame hCB, ?_, ?_, ?_, initPC, initActive⟩
    · rw [hh, Function.update_self]
    · intro node hn
      omega
    · intro tool ht
      omega
  obtain ⟨scanClock, hscan, scanReady, scanFrame⟩ := leaf_outer_scan_partial q full CB P before input.raw
    hlayout containing start code initialized ready (preparedSize q full) le_rfl
  let scanned := natRun rom containing scanClock initialized
  let after := runOps rom (scanBoundedTest 2 19 (start + 191)) scanned
  have endPC : after.pc = 5 * (start + 191) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) (preparedSize q full) 2 19 (start + 191) scanned
      scanReady.input.address scanReady.input.nodes scanReady.node_cell, Nat.sub_self, ite_eq_left rfl]
  have endActive : after.halted = false := (runOps_halted rom _ scanned).trans scanReady.active
  have endFrame : ScanFrame q full CB P scanned after := fun _ _ => rfl
  have initRun : natRun rom containing 4 before = initialized :=
    scan_chunk_run rom containing start code .initialize before
      (by simpa only [scanChunkOffset, Nat.add_zero] using hpc) ha
  have scannedRun : natRun rom containing (4 + scanClock) before = scanned :=
    (natRun_add rom containing 4 scanClock before).trans
      (congrArg (natRun rom containing scanClock) initRun)
  have endTestRun : natRun rom containing 9 scanned = after :=
    scan_chunk_run rom containing start code .outerTest scanned scanReady.pc scanReady.active
  have actual : natRun (rawIncidenceROM q full) containing (4 + scanClock + 9) before = after := by
    change natRun rom containing (4 + scanClock + 9) before = after
    exact (natRun_add rom containing (4 + scanClock) 9 before).trans
      ((congrArg (natRun rom containing 9) scannedRun).trans endTestRun)
  refine ⟨4 + scanClock + 9, by omega, ?_⟩
  rw [actual]
  have endInput : ScanInput q full CB P after :=
    ScanInput.of_frame scanReady.input hlayout endFrame scanReady.input.address
  refine ⟨endInput, ?_, ?_, (frame.trans scanFrame).trans endFrame,
    scanReady.input.address, endPC, endActive⟩
  · intro node
    exact scanReady.leaves node node.isLt
  · intro tool
    have htool : singletonIndex q full tool < preparedSize q full :=
      (IndexedStaticMetadata.singletonNode q full tool).isLt
    have h := scanReady.tools tool htool
    have heapEq : after.heap =
        (natRun (rawIncidenceROM q full) containing scanClock initialized).heap := rfl
    have finalTool : after.heap (fieldAddress P full.length (preparedSize q full) .tool tool.val) =
        singletonIndex q full tool + 1 :=
      (congrFun heapEq (fieldAddress P full.length (preparedSize q full) .tool tool.val)).trans h
    simpa only [IndexedStaticMetadata.buildPositive_tool_get, singletonIndex] using finalTool

theorem leaf_tool_steps_linear_product (q t clock : Nat)
    (hc : clock ≤ 13 + t * (67 + 116 * q)) : clock ≤ 200 * (t + 1) * (q + 1) := by
  nlinarith

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
