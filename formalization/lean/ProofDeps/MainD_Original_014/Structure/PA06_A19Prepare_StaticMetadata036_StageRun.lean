module

public import Structure.PA06_A19Prepare_StaticMetadata036_StageNode

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Complete actual202-op stage constructor. All N stages, t candidate
nodes, and q incidence comparisons are executed by the three nested loops.
Final optional IDs are proved equal to the original stageNodes, including
empty/repeated stages. The fixed Word lift remains a separate obligation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass loadRel storeRel setRel)

theorem stageRowInitialize_effect (rom : PhysicalROM) (CB P N t stage : Nat) (state : NatState)
    (hCB : state.register .address = CB) (hbase : state.heap (CB + 6) = 4 + P)
    (ht : state.heap (CB + 2) = t) (hs : state.heap (CB + 22) = stage) :
    let after := runOps rom stageRowInitialize state
    after.register .address = CB ∧ after.heap = Function.update
      (Function.update state.heap (fieldAddress P N t .stage stage) 0) (CB + 19) 0 := by
  simp [stageRowInitialize, loadRel, setRel, storeRel, storeField, fieldPointer,
    fieldPointerLead, fieldPointerExtra, fieldAddress, fieldFactor, fieldExtra,
    runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    hCB, hbase, ht, hs, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
  congr 2
  omega

theorem stage_row_init_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat) (reference : NatState)
    (stage : Fin full.length) (pointer nextPointer : Nat) (before after : NatState)
    (ready : StageOuterReady q full CB P reference stage.val pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = Function.update (Function.update before.heap
      (fieldAddress P full.length (preparedSize q full) .stage stage.val) 0) (CB + 19) 0)
    (hCB : after.register .address = CB) (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    StageNodeReady q full CB P reference stage 0 nextPointer after ∧ StageFrame q full CB P before after := by
  have below := stage_region_below_control q full CB P hlayout
  have hs := stage.isLt
  have hstage : fieldAddress P full.length (preparedSize q full) .stage stage.val < CB := by
    unfold fieldAddress fieldFactor fieldExtra at below ⊢
    omega
  have frame : StageFrame q full CB P before after := by
    intro address hn
    have h19 : address ≠ CB + 19 := by unfold StageAllowed at hn; omega
    have hst : address ≠ fieldAddress P full.length (preparedSize q full) .stage stage.val := by
      unfold StageAllowed fieldAddress fieldFactor fieldExtra at *
      omega
    rw [hh]
    simp [h19, hst]
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_stageFrame ready.input hlayout frame hCB
  · rw [hh]; simp (disch := omega) [ready.stage_cell]
  · rw [hh, Function.update_self]
  · rw [hh]; simp (disch := omega) [scanWinner]
  · intro earlier he
    have he' := earlier.isLt
    have ha' : fieldAddress P full.length (preparedSize q full) .stage earlier.val < CB := by
      unfold fieldAddress fieldFactor fieldExtra at below ⊢
      omega
    have hcontrol : fieldAddress P full.length (preparedSize q full) .stage earlier.val ≠ CB + 19 := by
      omega
    have hne : fieldAddress P full.length (preparedSize q full) .stage earlier.val ≠
        fieldAddress P full.length (preparedSize q full) .stage stage.val := by
      simp only [fieldAddress]
      omega
    rw [hh, Function.update_of_ne hcontrol, Function.update_of_ne hne]
    exact ready.stages earlier he
  · exact hpc
  · exact ha

section Actual
variable (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
  (reference : NatState) (referenceData : RawCardData q full CB reference)
  (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
  (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)

include referenceData hlayout code

theorem stage_node_scan_partial (stage : Fin full.length) (before : NatState)
    (ready : StageNodeReady q full CB P reference stage 0 (5 * (start + 34)) before)
    (count : Nat) (hc : count ≤ preparedSize q full) :
    ∃ clock ≤ count * (63 + 90 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageNodeReady q full CB P reference stage count (5 * (start + 34)) after ∧ StageFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨0, by omega, ready, StageFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, hp, previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing previousClock before
    have within : count < preparedSize q full := by omega
    obtain ⟨nextClock, hn, nextReady, nextFrame⟩ := stage_node_iteration q full CB P reference referenceData
      hlayout containing start code stage ⟨count, within⟩ previous previousReady
    refine ⟨previousClock + nextClock, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · rw [natRun_add]
      exact ⟨nextReady, previousFrame.trans nextFrame⟩

omit referenceData in
theorem stage_row_initialize (stage : Fin full.length) (before : NatState)
    (ready : StageOuterReady q full CB P reference stage.val (5 * (start + 4)) before) :
    let after := natRun (rawIncidenceROM q full) containing 30 before
    StageNodeReady q full CB P reference stage 0 (5 * (start + 34)) after ∧ StageFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 0 22 (start + 202)) before
  have htPC : tested.pc = 5 * (start + 13) := by
    rw [scanBoundedTest_pc rom CB full.length stage.val 0 22 (start + 202) before
      ready.input.address ready.input.stages ready.stage_cell, ite_eq_right (by have hs := stage.isLt; omega), ready.pc]
    omega
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  let after := runOps rom stageRowInitialize tested
  have effect := stageRowInitialize_effect rom CB P full.length (preparedSize q full) stage.val tested
    ready.input.address ready.input.base ready.input.nodes ready.stage_cell
  have hpc : after.pc = 5 * (start + 34) := by
    rw [runOps_pc rom _ tested (by simp [stageRowInitialize, loadRel, storeField, fieldPointer,
      fieldPointerLead, fieldPointerExtra, setRel, storeRel, NoJump]), htPC,
      show stageRowInitialize.length = 21 from rfl]
    omega
  have next := stage_row_init_ready q full CB P reference stage (5 * (start + 4)) (5 * (start + 34)) before after
    ready hlayout effect.2 effect.1 hpc ((runOps_halted rom _ tested).trans htActive)
  have testedRun : natRun (rawIncidenceROM q full) containing 9 before = tested :=
    stage_chunk_run rom containing start code .stageTest before ready.pc ready.active
  have rowRun : natRun (rawIncidenceROM q full) containing 21 tested = after :=
    stage_chunk_run rom containing start code .rowInitialize tested htPC htActive
  rw [show (30 : Nat) = 9 + 21 by decide, natRun_add, testedRun, rowRun]
  exact next

omit referenceData in
theorem stage_row_finish (stage : Fin full.length) (before : NatState)
    (ready : StageNodeReady q full CB P reference stage (preparedSize q full) (5 * (start + 34)) before) :
    let after := natRun (rawIncidenceROM q full) containing 20 before
    StageOuterReady q full CB P reference (stage.val + 1) (5 * (start + 4)) after ∧ StageFrame q full CB P before after := by
  let rom := rawIncidenceROM q full
  let tested := runOps rom (scanBoundedTest 2 19 (start + 191)) before
  have htPC : tested.pc = 5 * (start + 191) := by
    rw [scanBoundedTest_pc rom CB (preparedSize q full) (preparedSize q full) 2 19 (start + 191) before
      ready.input.address ready.input.nodes ready.node_cell, Nat.sub_self, ite_eq_left rfl]
  have htActive : tested.halted = false := (runOps_halted rom _ before).trans ready.active
  let after := runOps rom (stageOuterTail start) tested
  have tail := stageTail_effect rom CB stage.val 22 (start + 4) tested ready.input.address ready.stage_cell
  have hh : after.heap = Function.update before.heap (CB + 22) (stage.val + 1) := tail.2.1
  have frame := stage_control_frame q full CB P before after (Or.inr (Or.inr (Or.inl rfl))) hh
  have below := stage_region_below_control q full CB P hlayout
  have next : StageOuterReady q full CB P reference (stage.val + 1) (5 * (start + 4)) after := by
    constructor
    · exact ScanInput.of_stageFrame ready.input hlayout frame tail.1
    · rw [hh, Function.update_self]
    · intro earlier he
      have he' := earlier.isLt
      have ha' : fieldAddress P full.length (preparedSize q full) .stage earlier.val < CB := by
        unfold fieldAddress fieldFactor fieldExtra at below ⊢
        omega
      rw [hh, Function.update_of_ne (by omega)]
      by_cases hprev : earlier.val < stage.val
      · exact ready.stages earlier hprev
      · have heq : earlier = stage := Fin.ext (by omega)
        subst earlier
        exact ready.current_stage
    · exact tail.2.2.1
    · exact (tail.2.2.2).trans htActive
  have testedRun : natRun (rawIncidenceROM q full) containing 9 before = tested :=
    stage_chunk_run rom containing start code .nodeTest before ready.pc ready.active
  have tailRun : natRun (rawIncidenceROM q full) containing 11 tested = after :=
    stage_chunk_run rom containing start code .outerTail tested htPC htActive
  rw [show (20 : Nat) = 9 + 11 by decide, natRun_add, testedRun, tailRun]
  exact ⟨next, frame⟩

theorem stage_row_iteration (stage : Fin full.length) (before : NatState)
    (ready : StageOuterReady q full CB P reference stage.val (5 * (start + 4)) before) :
    ∃ clock ≤ 50 + preparedSize q full * (63 + 90 * q),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageOuterReady q full CB P reference (stage.val + 1) (5 * (start + 4)) after ∧ StageFrame q full CB P before after := by
  let initialized := natRun (rawIncidenceROM q full) containing 30 before
  obtain ⟨initReady, initFrame⟩ := stage_row_initialize q full CB P reference hlayout containing start code stage before ready
  obtain ⟨scanClock, hscan, scanReady, scanFrame⟩ := stage_node_scan_partial q full CB P reference referenceData
    hlayout containing start code stage initialized initReady (preparedSize q full) le_rfl
  let scanned := natRun (rawIncidenceROM q full) containing scanClock initialized
  have finish := stage_row_finish q full CB P reference hlayout containing start code stage scanned scanReady
  refine ⟨30 + scanClock + 20, by omega, ?_⟩
  rw [natRun_add, natRun_add]
  exact ⟨finish.1, (initFrame.trans scanFrame).trans finish.2⟩

theorem stage_outer_scan_partial (before : NatState)
    (ready : StageOuterReady q full CB P reference 0 (5 * (start + 4)) before)
    (count : Nat) (hc : count ≤ full.length) :
    ∃ clock ≤ count * (50 + preparedSize q full * (63 + 90 * q)),
      let after := natRun (rawIncidenceROM q full) containing clock before
      StageOuterReady q full CB P reference count (5 * (start + 4)) after ∧ StageFrame q full CB P before after := by
  revert hc
  induction count with
  | zero =>
    intro _
    exact ⟨0, by omega, ready, StageFrame.refl q full CB P before⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, hp, previousReady, previousFrame⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing previousClock before
    obtain ⟨nextClock, hn, nextReady, nextFrame⟩ := stage_row_iteration q full CB P reference referenceData
      hlayout containing start code ⟨count, by omega⟩ previous previousReady
    refine ⟨previousClock + nextClock, ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · rw [natRun_add]
      exact ⟨nextReady, previousFrame.trans nextFrame⟩

end Actual

/-- Complete actual202 Nat producer, derived from original raw data and
actual cached ord values. Neither stageNodes nor full support equality is
passed in. All stages receive their original exact optional node encoding. -/
theorem stage_build (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (CB P : Nat)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (before : NatState) (input : ScanInput q full CB P before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hpc : before.pc = 5 * start) (ha : before.halted = false) :
    ∃ clock ≤ 13 + full.length * (50 + preparedSize q full * (63 + 90 * q)),
      let after := natRun (rawIncidenceROM q full) containing clock before
      ScanInput q full CB P after ∧
      (∀ stage : Fin full.length,
        after.heap (fieldAddress P full.length (preparedSize q full) .stage stage.val) =
          encodedNode (prepareNormalization q full).indexed ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage)) ∧
      StageFrame q full CB P before after ∧ after.register .address = CB ∧
      after.pc = 5 * (start + 202) ∧ after.halted = false := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom stageInitialize before
  have hh : initialized.heap = Function.update before.heap (CB + 22) 0 := by
    simp [initialized, stageInitialize, PA06A19PrepareChildrenCache023.setRel_heap, input.address]
  have hCB : initialized.register .address = CB := input.address
  have frame := stage_control_frame q full CB P before initialized (Or.inr (Or.inr (Or.inl rfl))) hh
  have initPC : initialized.pc = 5 * (start + 4) := by
    rw [runOps_pc rom _ before (by simp [stageInitialize, setRel, storeRel, NoJump]), hpc,
      show stageInitialize.length = 4 from rfl]
    omega
  have initActive : initialized.halted = false := (runOps_halted rom _ before).trans ha
  have ready : StageOuterReady q full CB P before 0 (5 * (start + 4)) initialized := by
    refine ⟨ScanInput.of_stageFrame input hlayout frame hCB, ?_, ?_, initPC, initActive⟩
    · rw [hh, Function.update_self]
    · intro stage hs
      omega
  obtain ⟨scanClock, hscan, scanReady, scanFrame⟩ := stage_outer_scan_partial q full CB P before input.raw
    hlayout containing start code initialized ready full.length le_rfl
  let scanned := natRun rom containing scanClock initialized
  let after := runOps rom (scanBoundedTest 0 22 (start + 202)) scanned
  have endPC : after.pc = 5 * (start + 202) := by
    rw [scanBoundedTest_pc rom CB full.length full.length 0 22 (start + 202) scanned
      scanReady.input.address scanReady.input.stages scanReady.stage_cell, Nat.sub_self, ite_eq_left rfl]
  have endActive : after.halted = false := (runOps_halted rom _ scanned).trans scanReady.active
  have endFrame : StageFrame q full CB P scanned after := fun _ _ => rfl
  have initRun : natRun rom containing 4 before = initialized :=
    stage_chunk_run rom containing start code .initialize before
      (by simpa only [stageChunkOffset, Nat.add_zero] using hpc) ha
  have scannedRun : natRun rom containing (4 + scanClock) before = scanned :=
    (natRun_add rom containing 4 scanClock before).trans
      (congrArg (natRun rom containing scanClock) initRun)
  have endTestRun : natRun rom containing 9 scanned = after :=
    stage_chunk_run rom containing start code .stageTest scanned scanReady.pc scanReady.active
  have actual : natRun (rawIncidenceROM q full) containing (4 + scanClock + 9) before = after := by
    change natRun rom containing (4 + scanClock + 9) before = after
    exact (natRun_add rom containing (4 + scanClock) 9 before).trans
      ((congrArg (natRun rom containing 9) scannedRun).trans endTestRun)
  refine ⟨4 + scanClock + 9, by omega, ?_⟩
  rw [actual]
  have endInput : ScanInput q full CB P after :=
    ScanInput.of_stageFrame scanReady.input hlayout endFrame scanReady.input.address
  refine ⟨endInput, ?_, (frame.trans scanFrame).trans endFrame, scanReady.input.address, endPC, endActive⟩
  intro stage
  exact (scanReady.stages stage stage.isLt).trans (stageScan_original q full hq CB before input.raw stage)

theorem stage_steps_treeWork (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (clock : Nat)
    (hc : clock ≤ 13 + full.length * (50 + preparedSize q full * (63 + 90 * q))) :
    clock ≤ 300 * treeWork full.length q := by
  let N := full.length
  let t := preparedSize q full
  let M := N + q + 1
  have ht : t ≤ M := prepared_indexed_size_le q full
  have hN : N ≤ M := by dsimp only [M]; omega
  have hM : M ≤ M ^ 2 := by dsimp only [M]; nlinarith
  have hMq : M ^ 2 ≤ M ^ 2 * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M ^ 2) (show 1 ≤ q by omega)
  have hNq : N ≤ M ^ 2 * q := (hN.trans hM).trans hMq
  have hNt : N * t ≤ M ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hN ht
  have hNtq := Nat.mul_le_mul_right q hNt
  have hNt' : N * t ≤ M ^ 2 * q := hNt.trans hMq
  have hpos : 0 < M ^ 2 * q := Nat.mul_pos (pow_pos (by dsimp only [M]; omega) 2) hq
  change clock ≤ 300 * (M ^ 2 * q)
  change clock ≤ 13 + N * (50 + t * (63 + 90 * q)) at hc
  nlinarith

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
