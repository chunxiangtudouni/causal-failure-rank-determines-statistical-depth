module

public import Structure.PA06_A19Prepare_ChildrenCache023_Data

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled children-producer loop states. The pure ascending
list identities come from the existing childPrefix/flatPrefix theory;
this file starts their connection to actual fetched code. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix

abbrev Written := RawCandidateSerializedChildrenRun.Written

def rowList (q : Nat) (full : List (Finset (Fin q))) (parent child : Nat) : List Nat :=
  childPrefix (preparedSize q full) (parentWord q full) parent child

def beforeList (q : Nat) (full : List (Finset (Fin q))) (parent : Nat) : List Nat :=
  flatPrefix (preparedSize q full) (parentWord q full) parent

def scanList (q : Nat) (full : List (Finset (Fin q))) (parent child : Nat) : List Nat :=
  beforeList q full parent ++ rowList q full parent child

structure Controls (q : Nat) (full : List (Finset (Fin q))) (CB pointer : Nat) (state : NatState) : Prop where
  input : InputData q full CB state
  degree_base : state.heap (CB + 67) = degreeBase CB (mass q full)
  children_base : state.heap (CB + 68) = childrenBase CB (mass q full) (preparedSize q full)
  size_cell : state.heap (CB + 70) = preparedSize q full
  pc : state.pc = pointer
  active : state.halted = false

structure OuterReady (q : Nat) (full : List (Finset (Fin q))) (CB parent pointer : Nat) (state : NatState) : Prop where
  controls : Controls q full CB pointer state
  parent_cell : state.heap (CB + 64) = parent
  flat_cell : state.heap (CB + 66) = (beforeList q full parent).length
  degrees : ∀ node < parent,
    state.heap (degreeBase CB (mass q full) + node) = (childIDs (preparedSize q full) (parentWord q full) node).length
  children : Written (childrenBase CB (mass q full) (preparedSize q full)) (beforeList q full parent) state

structure InnerReady (q : Nat) (full : List (Finset (Fin q))) (CB parent child pointer : Nat) (state : NatState) : Prop where
  controls : Controls q full CB pointer state
  parent_cell : state.heap (CB + 64) = parent
  child_cell : state.heap (CB + 65) = child
  degree_cell : state.heap (CB + 69) = (rowList q full parent child).length
  flat_cell : state.heap (CB + 66) = (scanList q full parent child).length
  degrees : ∀ node < parent,
    state.heap (degreeBase CB (mass q full) + node) = (childIDs (preparedSize q full) (parentWord q full) node).length
  children : Written (childrenBase CB (mass q full) (preparedSize q full)) (scanList q full parent child) state

theorem initial_frame {q : Nat} {full : List (Finset (Fin q))} {CB : Nat}
    {before after : NatState}
    (hh : after.heap = Function.update (Function.update (Function.update (Function.update (Function.update before.heap
        (CB + 70) (preparedSize q full)) (CB + 67) (degreeBase CB (mass q full)))
      (CB + 68) (childrenBase CB (mass q full) (preparedSize q full))) (CB + 64) 0) (CB + 66) 0) :
    Frame q full CB before after := by
  intro address haddress
  rw [hh]
  have h := haddress.1
  simp (disch := omega)

theorem initialize_ready (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB pointer : Nat)
    (before after : NatState) (input : InputData q full CB before)
    (hh : after.heap = (runOps rom initializeCache before).heap)
    (hCB : after.register .address = before.register .address)
    (hp : after.pc = pointer) (ha : after.halted = false) :
    OuterReady q full CB 0 pointer after ∧ Frame q full CB before after := by
  have he := initializeCache_heap rom CB (mass q full) (preparedSize q full) before
    input.address input.mass_cell input.node_cell
  have hheap := hh.trans he
  have hf := initial_frame hheap
  refine ⟨?_, hf⟩
  constructor
  · refine ⟨input.of_frame hf hCB, ?_, ?_, ?_, hp, ha⟩
    · rw [hheap]
      simp
    · rw [hheap]
      simp
    · rw [hheap]
      simp
  · rw [hheap]
    simp
  · rw [hheap]
    simp [beforeList, flatPrefix_zero]
  · intro node hn
    omega
  · exact RawCandidateSerializedChildrenRun.Written.nil _ after

/-- First actual32-op phase, including fetched execution and ACTIVE PC.
Its source M/t and all output pointers are derived from the original copied
cache; no degree/children values are yet claimed at this boundary. -/
theorem initialize_phase (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
    (CB : Nat) (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (state : NatState) (input : InputData q full CB state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let after := natRun rom containing 32 state
    OuterReady q full CB 0 (5 * (start + 32)) after ∧ Frame q full CB state after := by
  have hr := chunk_run rom containing start code .initialize state (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha
  change natRun rom containing 32 state = runOps rom initializeCache state at hr
  rw [hr]
  apply initialize_ready rom q full CB (5 * (start + 32)) state _ input rfl
    (initializeCache_address rom state) ?_ ((runOps_halted rom _ state).trans ha)
  rw [runOps_pc rom _ state (by
    simp [initializeCache, loadRel, storeRel, setRel, NoJump]), initializeCache_length, hpc]
  omega

theorem Controls.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {CB pointer nextPointer : Nat}
    {before after : NatState} (controls : Controls q full CB pointer before)
    (hh : after.heap = before.heap) (hCB : after.register .address = before.register .address)
    (hp : after.pc = nextPointer) (ha : after.halted = false) : Controls q full CB nextPointer after := by
  have hf : Frame q full CB before after := fun address _ => congrFun hh address
  refine ⟨controls.input.of_frame hf hCB, ?_, ?_, ?_, hp, ha⟩
  · rw [hh]
    exact controls.degree_base
  · rw [hh]
    exact controls.children_base
  · rw [hh]
    exact controls.size_cell

theorem OuterReady.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {CB parent pointer nextPointer : Nat}
    {before after : NatState} (ready : OuterReady q full CB parent pointer before)
    (hh : after.heap = before.heap) (hCB : after.register .address = before.register .address)
    (hp : after.pc = nextPointer) (ha : after.halted = false) : OuterReady q full CB parent nextPointer after := by
  refine ⟨ready.controls.of_heap_eq hh hCB hp ha, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    exact ready.parent_cell
  · rw [hh]
    exact ready.flat_cell
  · intro node hn
    rw [hh]
    exact ready.degrees node hn
  · exact RawCandidateSerializedChildrenRun.Written.of_heap_eq ready.children hh

theorem InnerReady.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {CB parent child pointer nextPointer : Nat}
    {before after : NatState} (ready : InnerReady q full CB parent child pointer before)
    (hh : after.heap = before.heap) (hCB : after.register .address = before.register .address)
    (hp : after.pc = nextPointer) (ha : after.halted = false) : InnerReady q full CB parent child nextPointer after := by
  refine ⟨ready.controls.of_heap_eq hh hCB hp ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hh]
    exact ready.parent_cell
  · rw [hh]
    exact ready.child_cell
  · rw [hh]
    exact ready.degree_cell
  · rw [hh]
    exact ready.flat_cell
  · intro node hn
    rw [hh]
    exact ready.degrees node hn
  · exact RawCandidateSerializedChildrenRun.Written.of_heap_eq ready.children hh

theorem row_initialize_ready (q : Nat) (full : List (Finset (Fin q))) (CB parent pointer nextPointer : Nat)
    {before after : NatState} (ready : OuterReady q full CB parent pointer before)
    (hh : after.heap = Function.update (Function.update before.heap (CB + 65) 0) (CB + 69) 0)
    (hCB : after.register .address = before.register .address)
    (hp : after.pc = nextPointer) (ha : after.halted = false) :
    InnerReady q full CB parent 0 nextPointer after ∧ Frame q full CB before after := by
  have hf : Frame q full CB before after := by
    intro address haddress
    have h := haddress.1
    rw [hh]
    simp (disch := omega)
  refine ⟨?_, hf⟩
  constructor
  · refine ⟨ready.controls.input.of_frame hf hCB, ?_, ?_, ?_, hp, ha⟩
    · rw [hh]
      simpa using ready.controls.degree_base
    · rw [hh]
      simpa using ready.controls.children_base
    · rw [hh]
      simpa using ready.controls.size_cell
  · rw [hh]
    simpa using ready.parent_cell
  · rw [hh]
    simp
  · rw [hh]
    simp [rowList, childPrefix_zero]
  · rw [hh]
    simpa [scanList, rowList, childPrefix_zero] using ready.flat_cell
  · intro node hn
    rw [hh]
    simpa (disch := omega) [Function.update_apply, degreeBase] using ready.degrees node hn
  · intro position hposition
    rw [hh]
    have hpos : position < (beforeList q full parent).length := by
      simpa [scanList, rowList, childPrefix_zero] using hposition
    simpa (disch := omega) [Function.update_apply, childrenBase, degreeBase,
      scanList, rowList, childPrefix_zero] using ready.children position hpos

/-- One real outer guard and row initializer, preserving the copied cache
and previous outputs while entering the true inner-scan PC49. -/
theorem row_initialize (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (parent : Nat) (state : NatState) (ready : OuterReady q full CB parent (5 * (start + 32)) state)
    (hn : parent < preparedSize q full) :
    let after := natRun rom containing 17 state
    InnerReady q full CB parent 0 (5 * (start + 49)) after ∧ Frame q full CB state after := by
  let tested := runOps rom (boundedTest 64 (start + 144)) state
  have htPC : tested.pc = 5 * (start + 41) := by
    rw [branch_pc rom CB (preparedSize q full) parent 64 (start + 144) state
      ready.controls.input.address ready.controls.size_cell ready.parent_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hn), ready.controls.pc]
    omega
  have htActive : tested.halted = false := (runOps_halted rom _ state).trans ready.controls.active
  have htHeap : tested.heap = state.heap := rfl
  have htCB : tested.register .address = state.register .address := rfl
  have rt := ready.of_heap_eq htHeap htCB htPC htActive
  have hrow := row_initialize_ready q full CB parent (5 * (start + 41)) (5 * (start + 49))
    (before := tested) (after := runOps rom initializeRow tested) rt
    (by rw [initializeRow_heap, rt.controls.input.address])
    (initializeRow_address rom tested) (by
      rw [runOps_pc rom _ tested (by simp [initializeRow, setRel, storeRel, NoJump]),
        initializeRow_length, htPC]
      omega) ((runOps_halted rom _ tested).trans htActive)
  have htestRun := chunk_run rom containing start code .outerTest state ready.controls.pc ready.controls.active
  have hrowRun := chunk_run rom containing start code .initializeRow tested htPC htActive
  change natRun rom containing 9 state = tested at htestRun
  change natRun rom containing 8 tested = runOps rom initializeRow tested at hrowRun
  rw [show 17 = 9 + 8 from rfl, natRun_add, htestRun, hrowRun]
  exact ⟨hrow.1, (show Frame q full CB state tested from fun address _ => rfl).trans hrow.2⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
