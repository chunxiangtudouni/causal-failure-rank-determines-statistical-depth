module

public import Structure.PA06_A19Prepare_ChildrenCache023_WordChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled actual children-loop safety composition. Layout is
only real numeric allocation/code data, not a run-safety or output premise.
The final concrete word theorem must instantiate it from the original
F8192/width32 geometry, and every semantic state follows the actual Nat run. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m

structure Layout (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) : Prop where
  positive : 0 < q
  laminar : LaminarSchedule full
  code : CodeAt containing start
  room : highCacheEnd CB (mass q full) < H
  heap_bound : H ≤ B
  code_bound : 5 * containing.length ≤ B

theorem Layout.jump_bound {q : Nat} {full : List (Finset (Fin q))} {CB B H : Nat}
    {containing : List PackingOp} {start : Nat} (layout : Layout q full CB B H containing start)
    (offset : Nat) (ho : offset ≤ 144) : 5 * (start + offset) ≤ B := by
  have hc := layout.code.1
  have hb := layout.code_bound
  omega

theorem Layout.size_bound {q : Nat} {full : List (Finset (Fin q))} {CB B H : Nat}
    {containing : List PackingOp} {start : Nat} (_layout : Layout q full CB B H containing start) :
    preparedSize q full ≤ mass q full := prepared_indexed_size_le q full

theorem runSafe_zero (rom : PhysicalROM) (B H : Nat) (containing : List PackingOp)
    (state : NatState) (hr : RegistersLE B state) (ha : state.halted = false)
    (index : Nat) (hi : index ≤ containing.length) (hp : state.pc = 5 * index) :
    RunFacts B H rom containing 0 state := by
  constructor
  · constructor
    · intro count hc
      have he : count = 0 := by omega
      subst count
      exact ⟨hr, ha, index, hi, hp⟩
    · intro count hc
      omega
  · intro count hc
    have he : count = 0 := by omega
    subst count
    rfl

theorem initialize_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (state : NatState) (input : InputData q full CB state) (hr : RegistersLE B state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    RunFacts B H rom containing 32 state := by
  have he : CB + (mass q full * 4 + 532) = CB + 532 + 4 * mass q full := by omega
  have ht : state.heap (CB + (mass q full * 4 + 532)) = preparedSize q full :=
    (congrArg state.heap he).trans input.node_cell
  have numeric := initialize_numeric rom B H CB (mass q full) (preparedSize q full) state
    hr input.address input.mass_cell ht layout.size_bound layout.room layout.heap_bound
  exact chunk_safe rom B H containing start layout.code .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha numeric

theorem row_initialize_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent : Nat) (state : NatState) (ready : OuterReady q full CB parent (5 * (start + 32)) state)
    (hp : parent < preparedSize q full) (hr : RegistersLE B state) :
    RunFacts B H rom containing 17 state := by
  let tested := runOps rom (boundedTest 64 (start + 144)) state
  have numeric := boundedTest_numeric rom B H CB (mass q full) (preparedSize q full) parent 64 (start + 144) state
    hr ready.controls.input.address ready.controls.size_cell ready.parent_cell (by decide)
    layout.size_bound (hp.le.trans layout.size_bound) (layout.jump_bound 144 le_rfl) layout.room layout.heap_bound
  have testSafe := chunk_safe rom B H containing start layout.code .outerTest state ready.controls.pc ready.controls.active numeric
  change RunFacts B H rom containing 9 state at testSafe
  have testRun := chunk_run rom containing start layout.code .outerTest state ready.controls.pc ready.controls.active
  change natRun rom containing 9 state = tested at testRun
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 41) := by
    rw [branch_pc rom CB (preparedSize q full) parent 64 (start + 144) state
      ready.controls.input.address ready.controls.size_cell ready.parent_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hp), ready.controls.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ state).trans ready.controls.active
  have rowNumeric := initializeRow_numeric rom B H CB (mass q full) tested testRegs ready.controls.input.address layout.room layout.heap_bound
  have rowSafe := chunk_safe rom B H containing start layout.code .initializeRow tested testPC testActive rowNumeric
  change RunFacts B H rom containing (9 + 8) state
  exact RunFacts.add _ _ _ _ _ _ state testSafe (by rw [testRun]; exact rowSafe)

theorem child_iteration_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent child : Nat) (state : NatState) (ready : InnerReady q full CB parent child (5 * (start + 49)) state)
    (hp : parent < preparedSize q full) (hc : child < preparedSize q full) (hr : RegistersLE B state) :
    RunFacts B H rom containing (iterationSteps (parentWord q full) parent child) state := by
  let tested := runOps rom (boundedTest 65 (start + 122)) state
  have testNumeric := boundedTest_numeric rom B H CB (mass q full) (preparedSize q full) child 65 (start + 122) state
    hr ready.controls.input.address ready.controls.size_cell ready.child_cell (by decide)
    layout.size_bound (hc.le.trans layout.size_bound) (layout.jump_bound 122 (by decide)) layout.room layout.heap_bound
  have testSafe := chunk_safe rom B H containing start layout.code .innerTest state ready.controls.pc ready.controls.active testNumeric
  change RunFacts B H rom containing 9 state at testSafe
  have testRun := chunk_run rom containing start layout.code .innerTest state ready.controls.pc ready.controls.active
  change natRun rom containing 9 state = tested at testRun
  have testRegs : RegistersLE B tested := by
    have h := ((testSafe.1).final _ _ _ _ _).1
    rw [testRun] at h
    exact h
  have testPC : tested.pc = 5 * (start + 58) := by
    rw [branch_pc rom CB (preparedSize q full) child 65 (start + 122) state
      ready.controls.input.address ready.controls.size_cell ready.child_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hc), ready.controls.pc]
    omega
  have testActive : tested.halted = false := (runOps_halted rom _ state).trans ready.controls.active
  have testCB : tested.register .address = CB := ready.controls.input.address
  have testHeap : tested.heap = state.heap := rfl
  have hRead : tested.heap (CB + (533 + mass q full * 4 + child)) ≤ mass q full := by
    have he : CB + (533 + mass q full * 4 + child) = parentAddress CB (mass q full) child := by
      unfold parentAddress
      omega
    rw [he]
    exact (input_parent_le q full CB state ready.controls.input child hc).trans layout.size_bound
  have matchNumeric := matchTest_numeric rom B H CB (mass q full) parent child start tested testRegs testCB
    ready.controls.input.mass_cell ready.parent_cell ready.child_cell (hp.le.trans layout.size_bound)
    (hc.le.trans layout.size_bound) hRead (layout.jump_bound 84 (by decide)) layout.room layout.heap_bound
  have matchSafe := chunk_safe rom B H containing start layout.code .matchTest tested testPC testActive matchNumeric
  change RunFacts B H rom containing 23 tested at matchSafe
  let compared := runOps rom (matchTest start) tested
  have matchRun := chunk_run rom containing start layout.code .matchTest tested testPC testActive
  change natRun rom containing 23 tested = compared at matchRun
  have matchRegs : RegistersLE B compared := by
    have h := ((matchSafe.1).final _ _ _ _ _).1
    rw [matchRun] at h
    exact h
  have matchCB : compared.register .address = CB := testCB
  have comparedHeap : compared.heap = state.heap := rfl
  have matchActive : compared.halted = false := (runOps_halted rom _ tested).trans testActive
  have matchPC : compared.pc = if parentWord q full child = parent + 1 then 5 * (start + 84) else 5 * (start + 81) := by
    have h := match_pc rom CB (mass q full) parent child start tested testCB
      ready.controls.input.mass_cell ready.parent_cell ready.child_cell
    rw [testHeap, ready.controls.input.parents child hc, testPC] at h
    rw [h]
    split_ifs <;> omega
  have first := RunFacts.add _ _ _ _ 9 23 state testSafe (by rw [testRun]; exact matchSafe)
  have firstRun : natRun rom containing (9 + 23) state = compared := by rw [natRun_add, testRun, matchRun]
  by_cases heq : parentWord q full child = parent + 1
  · have hmPC : compared.pc = 5 * (start + 84) := by simpa only [heq, ite_true] using matchPC
    have hbounds := inner_ready_bounds q full layout.positive layout.laminar CB parent child _ state ready hp hc.le
    have hflat := matched_position_lt q full layout.positive layout.laminar CB parent child _ state ready hp hc heq
    have matNumeric := matched_numeric rom B H CB (mass q full) (preparedSize q full) child
      (state.heap (CB + 69)) (state.heap (CB + 66)) compared matchRegs matchCB ready.controls.children_base
      ready.child_cell rfl rfl layout.size_bound (hc.le.trans layout.size_bound)
      (hbounds.2.2.1.trans layout.size_bound) hflat layout.room layout.heap_bound
    have matSafe := chunk_safe rom B H containing start layout.code .matched compared hmPC matchActive matNumeric
    change RunFacts B H rom containing 27 compared at matSafe
    let written := runOps rom matched compared
    have matRun := chunk_run rom containing start layout.code .matched compared hmPC matchActive
    change natRun rom containing 27 compared = written at matRun
    have writtenRegs : RegistersLE B written := by
      have h := ((matSafe.1).final _ _ _ _ _).1
      rw [matRun] at h
      exact h
    have writtenPC : written.pc = 5 * (start + 111) := by
      rw [runOps_pc rom _ compared (by simp [matched, writeChild, incrementRel, loadRel, storeRel, NoJump]), matched_length, hmPC]
      omega
    have writtenActive : written.halted = false := (runOps_halted rom _ compared).trans matchActive
    have writtenCB : written.register .address = CB := matchCB
    have ptrRoom : CB + 71 ≤ compared.heap (CB + 68) := by
      rw [comparedHeap, ready.controls.children_base]
      unfold childrenBase degreeBase
      omega
    have writtenChild : written.heap (CB + 65) = child := by
      rw [matched_heap rom CB compared matchCB ptrRoom, comparedHeap, ready.controls.children_base, ready.child_cell]
      simp (disch := omega) [childrenBase, degreeBase]
      exact ready.child_cell
    have tailNumeric := innerTail_numeric rom B H CB (mass q full) child start written writtenRegs writtenCB
      writtenChild (hc.le.trans layout.size_bound) (layout.jump_bound 49 (by decide)) layout.room layout.heap_bound
    have tailSafe := chunk_safe rom B H containing start layout.code .innerTail written writtenPC writtenActive tailNumeric
    have later := RunFacts.add _ _ _ _ 27 11 compared matSafe (by rw [matRun]; exact tailSafe)
    have all := RunFacts.add _ _ _ _ (9 + 23) (27 + 11) state first (by rw [firstRun]; exact later)
    simpa only [iterationSteps, heq, ite_true] using all
  · have hmPC : compared.pc = 5 * (start + 81) := by simpa only [heq, ite_false] using matchPC
    have skipNumeric := skip_numeric rom B H (start + 111) compared matchRegs (layout.jump_bound 111 (by decide))
    have skipSafe := chunk_safe rom B H containing start layout.code .skip compared hmPC matchActive skipNumeric
    change RunFacts B H rom containing 3 compared at skipSafe
    let skipped := runOps rom (jumpTo (start + 111)) compared
    have skipRun := chunk_run rom containing start layout.code .skip compared hmPC matchActive
    change natRun rom containing 3 compared = skipped at skipRun
    have skipRegs : RegistersLE B skipped := by
      have h := ((skipSafe.1).final _ _ _ _ _).1
      rw [skipRun] at h
      exact h
    have skipPC : skipped.pc = 5 * (start + 111) := by simp [skipped, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    have skipActive : skipped.halted = false := (runOps_halted rom _ compared).trans matchActive
    have skipCB : skipped.register .address = CB := matchCB
    have tailNumeric := innerTail_numeric rom B H CB (mass q full) child start skipped skipRegs skipCB
      ready.child_cell (hc.le.trans layout.size_bound) (layout.jump_bound 49 (by decide)) layout.room layout.heap_bound
    have tailSafe := chunk_safe rom B H containing start layout.code .innerTail skipped skipPC skipActive tailNumeric
    have later := RunFacts.add _ _ _ _ 3 11 compared skipSafe (by rw [skipRun]; exact tailSafe)
    have all := RunFacts.add _ _ _ _ (9 + 23) (3 + 11) state first (by rw [firstRun]; exact later)
    simpa only [iterationSteps, heq, ite_false] using all

theorem child_scan_partial_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent : Nat) (state : NatState) (ready : InnerReady q full CB parent 0 (5 * (start + 49)) state)
    (hp : parent < preparedSize q full) (hr : RegistersLE B state) (count : Nat) (hc : count ≤ preparedSize q full) :
    RunFacts B H rom containing (childSteps q full parent count) state := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [childSteps, Finset.range_zero, Finset.sum_empty] using
      runSafe_zero rom B H containing state hr ready.controls.active (start + 49)
        (by have h := layout.code.1; omega) ready.controls.pc
  | succ count ih =>
    intro hc
    have hs := ih (by omega)
    let previous := natRun rom containing (childSteps q full parent count) state
    obtain ⟨rp, _frame⟩ := child_scan_partial rom q full layout.positive layout.laminar CB containing start layout.code
      parent state ready hp count (by omega)
    have reg := ((hs.1).final _ _ _ _ _).1
    have next := child_iteration_safe rom q full CB B H containing start layout parent count previous rp hp (by omega) reg
    rw [childSteps_succ]
    exact RunFacts.add _ _ _ _ _ _ state hs next

theorem child_scan_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent : Nat) (state : NatState) (ready : InnerReady q full CB parent 0 (5 * (start + 49)) state)
    (hp : parent < preparedSize q full) (hr : RegistersLE B state) :
    RunFacts B H rom containing (childSteps q full parent (preparedSize q full) + 9) state := by
  have hs := child_scan_partial_safe rom q full CB B H containing start layout parent state ready hp hr (preparedSize q full) le_rfl
  let previous := natRun rom containing (childSteps q full parent (preparedSize q full)) state
  obtain ⟨rp, _frame⟩ := child_scan_partial rom q full layout.positive layout.laminar CB containing start layout.code
    parent state ready hp (preparedSize q full) le_rfl
  have reg := ((hs.1).final _ _ _ _ _).1
  have num := boundedTest_numeric rom B H CB (mass q full) (preparedSize q full) (preparedSize q full) 65 (start + 122) previous
    reg rp.controls.input.address rp.controls.size_cell rp.child_cell (by decide) layout.size_bound layout.size_bound
    (layout.jump_bound 122 (by decide)) layout.room layout.heap_bound
  have last := chunk_safe rom B H containing start layout.code .innerTest previous rp.controls.pc rp.controls.active num
  exact RunFacts.add _ _ _ _ _ _ state hs last

theorem row_finish_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent : Nat) (state : NatState)
    (ready : InnerReady q full CB parent (preparedSize q full) (5 * (start + 122)) state)
    (hp : parent < preparedSize q full) (hr : RegistersLE B state) :
    RunFacts B H rom containing 22 state := by
  have hd : state.heap (CB + 69) ≤ mass q full :=
    ((inner_ready_bounds q full layout.positive layout.laminar CB parent (preparedSize q full) _ state ready hp le_rfl).2.2.1).trans layout.size_bound
  have num := outerTail_numeric rom B H CB (mass q full) parent (state.heap (CB + 69)) start state hr
    ready.controls.input.address ready.parent_cell rfl ready.controls.degree_base (hp.le.trans layout.size_bound) hd
    (layout.jump_bound 32 (by decide)) layout.room layout.heap_bound
  exact chunk_safe rom B H containing start layout.code .outerTail state ready.controls.pc ready.controls.active num

theorem row_iteration_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (parent : Nat) (state : NatState) (ready : OuterReady q full CB parent (5 * (start + 32)) state)
    (hp : parent < preparedSize q full) (hr : RegistersLE B state) :
    RunFacts B H rom containing (rowSteps q full parent) state := by
  have hi := row_initialize_safe rom q full CB B H containing start layout parent state ready hp hr
  let initialized := natRun rom containing 17 state
  obtain ⟨ri, _frame⟩ := row_initialize rom q full CB containing start layout.code parent state ready hp
  have hri := ((hi.1).final _ _ _ _ _).1
  have hc := child_scan_safe rom q full CB B H containing start layout parent initialized ri hp hri
  let scanned := natRun rom containing (childSteps q full parent (preparedSize q full) + 9) initialized
  obtain ⟨rs, _frame⟩ := child_scan rom q full layout.positive layout.laminar CB containing start layout.code parent initialized ri hp
  have hrs := ((hc.1).final _ _ _ _ _).1
  have hf := row_finish_safe rom q full CB B H containing start layout parent scanned rs hp hrs
  have combined := RunFacts.add _ _ _ _ 17 ((childSteps q full parent (preparedSize q full) + 9) + 22) state hi
    (RunFacts.add _ _ _ _ _ _ initialized hc hf)
  have ht : rowSteps q full parent = 17 + ((childSteps q full parent (preparedSize q full) + 9) + 22) := by unfold rowSteps; omega
  rw [ht]
  exact combined

theorem outer_scan_partial_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (state : NatState) (ready : OuterReady q full CB 0 (5 * (start + 32)) state)
    (hr : RegistersLE B state) (count : Nat) (hc : count ≤ preparedSize q full) :
    RunFacts B H rom containing (outerSteps q full count) state := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerSteps, Finset.range_zero, Finset.sum_empty] using
      runSafe_zero rom B H containing state hr ready.controls.active (start + 32)
        (by have h := layout.code.1; omega) ready.controls.pc
  | succ count ih =>
    intro hc
    have hs := ih (by omega)
    let previous := natRun rom containing (outerSteps q full count) state
    obtain ⟨rp, _frame⟩ := outer_scan_partial rom q full layout.positive layout.laminar CB containing start layout.code state ready count (by omega)
    have reg := ((hs.1).final _ _ _ _ _).1
    have next := row_iteration_safe rom q full CB B H containing start layout count previous rp (by omega) reg
    rw [outerSteps_succ]
    exact RunFacts.add _ _ _ _ _ _ state hs next

/-- Complete actual nested-run safety, derived from original cache data.
No caller supplies a proof that this entire execution is safe. -/
theorem build_safe (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB B H : Nat)
    (containing : List PackingOp) (start : Nat) (layout : Layout q full CB B H containing start)
    (state : NatState) (input : InputData q full CB state) (hr : RegistersLE B state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    RunFacts B H rom containing (totalSteps q full) state := by
  have hi := initialize_safe rom q full CB B H containing start layout state input hr hpc ha
  let initialized := natRun rom containing 32 state
  obtain ⟨ri, _frame⟩ := initialize_phase rom q full CB containing start layout.code state input hpc ha
  have hri := ((hi.1).final _ _ _ _ _).1
  have hs := outer_scan_partial_safe rom q full CB B H containing start layout initialized ri hri (preparedSize q full) le_rfl
  let scanned := natRun rom containing (outerSteps q full (preparedSize q full)) initialized
  obtain ⟨rs, _frame⟩ := outer_scan_partial rom q full layout.positive layout.laminar CB containing start layout.code initialized ri (preparedSize q full) le_rfl
  have hrs := ((hs.1).final _ _ _ _ _).1
  have num := boundedTest_numeric rom B H CB (mass q full) (preparedSize q full) (preparedSize q full) 64 (start + 144) scanned
    hrs rs.controls.input.address rs.controls.size_cell rs.parent_cell (by decide) layout.size_bound layout.size_bound
    (layout.jump_bound 144 le_rfl) layout.room layout.heap_bound
  have last := chunk_safe rom B H containing start layout.code .outerTest scanned rs.controls.pc rs.controls.active num
  have all := RunFacts.add _ _ _ _ 32 (outerSteps q full (preparedSize q full) + 9) state hi
    (RunFacts.add _ _ _ _ _ _ initialized hs last)
  simpa only [totalSteps, Nat.add_assoc] using all

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
