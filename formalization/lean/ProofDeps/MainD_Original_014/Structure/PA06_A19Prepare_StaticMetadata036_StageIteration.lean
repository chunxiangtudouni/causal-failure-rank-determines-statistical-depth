module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageState

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual90-step-bounded stage comparison iteration: real stage read,
frozen022 node query, streaming equality update and counter/backjump.
No comparison result or dense support matrix is a caller input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel)

def stageToolHeap (q : Nat) (full : List (Finset (Fin q))) (reference : NatState)
    (CB stage node tool : Nat) (heap : Nat → Nat) : Nat → Nat :=
  Function.update (Function.update (Function.update heap (CB + 24)
    (rawStageBit (rawIncidenceROM q full) stage tool)) (CB + 23)
      (bit (stageMatchTools (rawIncidenceROM q full) reference.heap CB (mass q full) stage node (tool + 1))))
        (CB + 20) (tool + 1)

theorem stage_tool_heap_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (pointer : Nat) (before after : NatState)
    (ready : StageToolReady q full CB P reference stage node tool.val pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = stageToolHeap q full reference CB stage.val node.val tool.val before.heap)
    (hCB : after.register .address = CB) (hpc : after.pc = pointer) (ha : after.halted = false) :
    StageToolReady q full CB P reference stage node (tool.val + 1) pointer after ∧ StageFrame q full CB P before after := by
  have frame : StageFrame q full CB P before after := by
    intro address hn
    have h20 : address ≠ CB + 20 := by unfold StageAllowed at hn; omega
    have h23 : address ≠ CB + 23 := by unfold StageAllowed at hn; omega
    have h24 : address ≠ CB + 24 := by unfold StageAllowed at hn; omega
    rw [hh]
    simp [stageToolHeap, h20, h23, h24]
  have below := stage_region_below_control q full CB P hlayout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_stageFrame ready.input hlayout frame hCB
  · rw [hh]
    simp [stageToolHeap, ready.stage_cell]
  · rw [hh]
    simp [stageToolHeap, ready.node_cell]
  · rw [hh]
    simp only [stageToolHeap, Function.update_self]
  · rw [hh]
    simp [stageToolHeap]
  · rw [hh]
    simpa (disch := omega) [stageToolHeap, Function.update_apply] using ready.current_stage
  · intro earlier he
    have he' := earlier.isLt
    have ha' : fieldAddress P full.length (preparedSize q full) .stage earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    rw [hh]
    simpa (disch := omega) [stageToolHeap, Function.update_apply] using ready.stages earlier he
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)

include referenceData hlayout code

theorem stage_tool_iteration (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId)
    (tool : Fin q) (before : NatState)
    (ready : StageToolReady q full CB P reference stage node tool.val (5 * (start + 51)) before) :
    ∃ clock ≤ 90,
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageToolReady q full CB P reference stage node (tool.val + 1) (5 * (start + 51)) after ∧
        StageFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 1 20 (start + 154)) before
  have htPC : tested.pc = 5 * (start + 60) := by
    rw [scanBoundedTest_pc rom CB q tool.val 1 20 (start + 154) before
      ready.input.address ready.input.tools ready.tool_cell, ite_eq_right (by have h := tool.isLt; omega), ready.pc]
    omega
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  have htRun : natRun rom containing 9 before = tested :=
    stage_chunk_run rom containing start code .toolTest before ready.pc ready.active
  let rawRead := runOps rom stageRead tested
  have raw := stageRead_effect rom CB stage.val tool.val q tested ready.input.address ready.stage_cell
    ready.tool_cell ready.input.tools (raw_header_q q full)
  have rawHeap : rawRead.heap = Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val) := raw.2
  have rawFrame := stage_control_frame q full CB P before rawRead
    (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) rawHeap
  have rawInput : ScanInput q full CB P rawRead := ScanInput.of_stageFrame ready.input hlayout rawFrame raw.1
  have rawPC : rawRead.pc = 5 * (start + 77) := by
    rw [runOps_pc rom _ tested (by simp [stageRead, loadRel, storeRel, NoJump]), htPC,
      show stageRead.length = 17 from rfl]
    omega
  have rawActive : rawRead.halted = false := (runOps_halted rom _ tested).trans htActive
  have rawRun : natRun rom containing 17 tested = rawRead :=
    stage_chunk_run rom containing start code .read tested htPC htActive
  have rawNode : rawRead.heap (CB + 19) = node.val := by rw [rawHeap]; simp [ready.node_cell]
  have rawTool : rawRead.heap (CB + 20) = tool.val := by rw [rawHeap]; simp [ready.tool_cell]
  let arguments := runOps rom scanArguments rawRead
  have args := scanArguments_effect rom CB node.val tool.val rawRead raw.1 rawNode rawTool
  have argumentsHeap : arguments.heap = rawRead.heap := args.2.2.2
  have argumentsRaw : RawCardData q full CB arguments :=
    RawCardData.of_children_frame rawInput.raw
      (fun address _ => congrFun argumentsHeap address)
  have argsPC : arguments.pc = 5 * (start + 83) := by
    rw [runOps_pc rom _ rawRead (by simp [scanArguments, loadRel, NoJump]), rawPC,
      show scanArguments.length = 6 from rfl]
    omega
  have argsActive : arguments.halted = false := (runOps_halted rom _ rawRead).trans rawActive
  have argsRun : natRun rom containing 6 rawRead = arguments :=
    stage_chunk_run rom containing start code .arguments rawRead rawPC rawActive
  let readClock := nodeReadClock full.length arguments.heap CB (mass q full) node.val tool.val
  let read := natRun rom containing readClock arguments
  have result := nodeBit_nat_read q full containing (start + 83) (stage_query_code containing start code)
    CB arguments argumentsRaw node tool argsPC argsActive args.1 args.2.1 args.2.2.1
  change read.register .value = rawCandidateBit rom
    (arguments.heap (rawOrdAddress CB (mass q full) node.val)) tool.val ∧
    read.register .fresh = tool.val ∧ read.register .address = CB ∧ read.heap = arguments.heap ∧
    read.pc = 5 * (start + 129) ∧ read.halted = false at result
  have readHeap : read.heap = Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val) :=
    result.2.2.2.1.trans rawHeap
  have readValue : read.register .value = rawCandidateBit rom
      (reference.heap (rawOrdAddress CB (mass q full) node.val)) tool.val := by
    rw [result.1]
    exact (rawNodeBit_eq_decode q full CB arguments argumentsRaw node tool).trans
      (rawNodeBit_eq_decode q full CB reference referenceData node tool).symm
  have readMatch : read.heap (CB + 23) = bit (stageMatchTools rom reference.heap CB (mass q full) stage.val node.val tool.val) := by
    rw [readHeap]
    simp [ready.match_cell, rom]
  have readStage : read.heap (CB + 24) = rawStageBit rom stage.val tool.val := by
    rw [readHeap, Function.update_self]
  let compared := runOps rom stageCompare read
  have compare := stageCompare_effect rom CB _ _ read result.2.2.1 readMatch readStage
  have compareHeap : compared.heap = Function.update
      (Function.update before.heap (CB + 24) (rawStageBit rom stage.val tool.val)) (CB + 23)
      (bit (stageMatchTools rom reference.heap CB (mass q full) stage.val node.val (tool.val + 1))) := by
    rw [compare.2, readHeap, readValue, bit_and_comparison]
    rfl
  have comparePC : compared.pc = 5 * (start + 143) := by
    rw [runOps_pc rom _ read (by simp [stageCompare, loadRel, storeRel, NoJump]), result.2.2.2.2.1,
      show stageCompare.length = 14 from rfl]
    omega
  have compareActive : compared.halted = false := (runOps_halted rom _ read).trans result.2.2.2.2.2
  have compareRun : natRun rom containing 14 read = compared :=
    stage_chunk_run rom containing start code .compare read result.2.2.2.2.1 result.2.2.2.2.2
  have compareTool : compared.heap (CB + 20) = tool.val := by
    rw [compareHeap]
    simp [ready.tool_cell]
  let after := runOps rom (stageToolTail start) compared
  have tail : after.register .address = CB ∧
      after.heap = Function.update compared.heap (CB + 20) (tool.val + 1) ∧
      after.pc = 5 * (start + 51) ∧ after.halted = compared.halted := by
    simpa only [after, stageToolTail, scanInnerTail] using
      (scanInnerTail_effect rom CB tool.val start compared compare.1 compareTool)
  have afterHeap : after.heap = stageToolHeap q full reference CB stage.val node.val tool.val before.heap := by
    rw [tail.2.1, compareHeap]
    rfl
  have next := stage_tool_heap_ready q full CB P reference stage node tool (5 * (start + 51)) before after
    ready hlayout afterHeap tail.1 tail.2.2.1 ((tail.2.2.2).trans compareActive)
  have tailRun : natRun rom containing 11 compared = after :=
    stage_chunk_run rom containing start code .toolTail compared comparePC compareActive
  refine ⟨9 + 17 + 6 + readClock + 14 + 11, ?_, ?_⟩
  · have hc := nodeReadClock_le full.length arguments.heap CB (mass q full) node.val tool.val
    change readClock ≤ 33 at hc
    omega
  · rw [natRun_add, natRun_add, natRun_add, natRun_add, natRun_add,
      htRun, rawRun, argsRun, compareRun, tailRun]
    exact next

end Actual
end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
