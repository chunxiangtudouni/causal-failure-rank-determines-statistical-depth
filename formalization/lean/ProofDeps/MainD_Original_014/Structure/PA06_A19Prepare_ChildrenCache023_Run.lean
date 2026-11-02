module

public import Structure.PA06_A19Prepare_ChildrenCache023_Invariants

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled full actual nested-loop candidate for the fixed144
children cache producer. No mathematical answer or whole-run safety is an
input; runtime data starts at the copied raw cache interface. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix
open scoped BigOperators

def childSteps (q : Nat) (full : List (Finset (Fin q))) (parent count : Nat) : Nat :=
  ∑ child ∈ Finset.range count, iterationSteps (parentWord q full) parent child

def rowSteps (q : Nat) (full : List (Finset (Fin q))) (parent : Nat) : Nat :=
  48 + childSteps q full parent (preparedSize q full)

def outerSteps (q : Nat) (full : List (Finset (Fin q))) (count : Nat) : Nat :=
  ∑ parent ∈ Finset.range count, rowSteps q full parent

def totalSteps (q : Nat) (full : List (Finset (Fin q))) : Nat :=
  32 + outerSteps q full (preparedSize q full) + 9

theorem childSteps_succ (q : Nat) (full : List (Finset (Fin q))) (parent count : Nat) :
    childSteps q full parent (count + 1) = childSteps q full parent count + iterationSteps (parentWord q full) parent count :=
  Finset.sum_range_succ _ _

theorem outerSteps_succ (q : Nat) (full : List (Finset (Fin q))) (count : Nat) :
    outerSteps q full (count + 1) = outerSteps q full count + rowSteps q full count := Finset.sum_range_succ _ _

theorem childSteps_le (q : Nat) (full : List (Finset (Fin q))) (parent count : Nat) :
    childSteps q full parent count ≤ 70 * count := by
  calc
    _ ≤ ∑ _child ∈ Finset.range count, 70 := Finset.sum_le_sum (fun _ _ => iterationSteps_le _ _ _)
    _ = _ := by simp [Nat.mul_comm]

theorem outerSteps_le (q : Nat) (full : List (Finset (Fin q))) (count : Nat) :
    outerSteps q full count ≤ count * (48 + 70 * preparedSize q full) := by
  calc
    _ ≤ ∑ _parent ∈ Finset.range count, (48 + 70 * preparedSize q full) := by
      apply Finset.sum_le_sum
      intro parent _
      have h := childSteps_le q full parent (preparedSize q full)
      unfold rowSteps
      omega
    _ = _ := by simp

theorem totalSteps_le (q : Nat) (full : List (Finset (Fin q))) :
    totalSteps q full ≤ 200 * (preparedSize q full + 1) ^ 2 := by
  have h := outerSteps_le q full (preparedSize q full)
  unfold totalSteps
  nlinarith

theorem row_finish_heap_ready (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (parent pointer nextPointer : Nat) {before after : NatState}
    (ready : InnerReady q full CB parent (preparedSize q full) pointer before) (hp : parent < preparedSize q full)
    (hh : after.heap = Function.update (Function.update before.heap
      (degreeBase CB (mass q full) + parent) (childIDs (preparedSize q full) (parentWord q full) parent).length)
        (CB + 64) (parent + 1))
    (hCB : after.register .address = before.register .address) (hpc : after.pc = nextPointer) (ha : after.halted = false) :
    OuterReady q full CB (parent + 1) nextPointer after ∧ Frame q full CB before after := by
  have hf : Frame q full CB before after := by
    intro address hout
    have htemp := hout.1
    have hne : address ≠ degreeBase CB (mass q full) + parent := by
      rcases hout.2 with hout | hout <;> unfold childrenBase at * <;> omega
    rw [hh, Function.update_of_ne (by omega : address ≠ CB + 64), Function.update_of_ne hne]
  have hlarge : CB + 71 ≤ degreeBase CB (mass q full) := by unfold degreeBase; omega
  refine ⟨?_, hf⟩
  constructor
  · refine ⟨ready.controls.input.of_frame hf hCB, ?_, ?_, ?_, hpc, ha⟩
    · rw [hh]
      simpa (disch := omega) [Function.update_apply] using ready.controls.degree_base
    · rw [hh]
      simpa (disch := omega) [Function.update_apply] using ready.controls.children_base
    · rw [hh]
      simpa (disch := omega) [Function.update_apply] using ready.controls.size_cell
  · rw [hh]
    simp
  · rw [hh, ← scanList_full]
    simpa (disch := omega) [Function.update_apply] using ready.flat_cell
  · intro node hn
    rw [hh]
    by_cases heq : node = parent
    · subst node
      simp (disch := omega)
    · have hold : node < parent := by omega
      simpa (disch := omega) [Function.update_apply] using ready.degrees node hold
  · rw [← scanList_full]
    intro position hposition
    rw [hh]
    simpa (disch := omega) [Function.update_apply, childrenBase] using ready.children position hposition

section Linked
variable (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q)))
  (hq : 0 < q) (hl : LaminarSchedule full) (CB : Nat)
  (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
include code hq hl

theorem child_scan_partial (parent : Nat) (state : NatState)
    (ready : InnerReady q full CB parent 0 (5 * (start + 49)) state)
    (hp : parent < preparedSize q full) (count : Nat) (hc : count ≤ preparedSize q full) :
    let after := natRun rom containing (childSteps q full parent count) state
    InnerReady q full CB parent count (5 * (start + 49)) after ∧ Frame q full CB state after := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [childSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show InnerReady q full CB parent 0 (5 * (start + 49)) state ∧ Frame q full CB state state from
        ⟨ready, Frame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hc
    obtain ⟨rp, hf⟩ := ih (by omega)
    let previous := natRun rom containing (childSteps q full parent count) state
    have hr := child_iteration rom q full hq hl CB containing start code parent count previous rp hp (by omega)
    dsimp only at hr
    dsimp only
    rw [childSteps_succ, natRun_add]
    exact ⟨hr.1, hf.trans hr.2⟩

theorem child_scan (parent : Nat) (state : NatState)
    (ready : InnerReady q full CB parent 0 (5 * (start + 49)) state) (hp : parent < preparedSize q full) :
    let after := natRun rom containing (childSteps q full parent (preparedSize q full) + 9) state
    InnerReady q full CB parent (preparedSize q full) (5 * (start + 122)) after ∧ Frame q full CB state after := by
  let previous := natRun rom containing (childSteps q full parent (preparedSize q full)) state
  obtain ⟨rp, hf⟩ := child_scan_partial rom q full hq hl CB containing start code parent state ready hp (preparedSize q full) le_rfl
  let finished := runOps rom (boundedTest 65 (start + 122)) previous
  have hpFinal : finished.pc = 5 * (start + 122) := by
    rw [branch_pc rom CB (preparedSize q full) (preparedSize q full) 65 (start + 122) previous
      rp.controls.input.address rp.controls.size_cell rp.child_cell, Nat.sub_self, ite_eq_left rfl]
  have ha : finished.halted = false := (runOps_halted rom _ previous).trans rp.controls.active
  have hr := chunk_run rom containing start code .innerTest previous rp.controls.pc rp.controls.active
  change natRun rom containing 9 previous = finished at hr
  rw [natRun_add, hr]
  exact ⟨rp.of_heap_eq rfl rfl hpFinal ha, hf.trans (show Frame q full CB previous finished from fun _ _ => rfl)⟩

omit hq hl in
theorem row_finish (parent : Nat) (state : NatState)
    (ready : InnerReady q full CB parent (preparedSize q full) (5 * (start + 122)) state)
    (hp : parent < preparedSize q full) :
    let after := natRun rom containing 22 state
    OuterReady q full CB (parent + 1) (5 * (start + 32)) after ∧ Frame q full CB state after := by
  have hptr : CB + 71 ≤ state.heap (CB + 67) := by rw [ready.controls.degree_base]; unfold degreeBase; omega
  have hh := outerTail_heap rom CB start state ready.controls.input.address hptr
  rw [ready.parent_cell, ready.controls.degree_base, ready.degree_cell] at hh
  have hrow : rowList q full parent (preparedSize q full) = childIDs (preparedSize q full) (parentWord q full) parent := rfl
  rw [hrow] at hh
  have heq : parent + degreeBase CB (mass q full) = degreeBase CB (mass q full) + parent := Nat.add_comm _ _
  rw [heq] at hh
  have hr := chunk_run rom containing start code .outerTail state ready.controls.pc ready.controls.active
  change natRun rom containing 22 state = runOps rom (outerTail start) state at hr
  rw [hr]
  exact row_finish_heap_ready q full CB parent _ _ ready hp hh
    (outerTail_address rom start state) (outerTail_pc rom start state)
    ((runOps_halted rom _ state).trans ready.controls.active)

theorem row_iteration (parent : Nat) (state : NatState)
    (ready : OuterReady q full CB parent (5 * (start + 32)) state) (hp : parent < preparedSize q full) :
    let after := natRun rom containing (rowSteps q full parent) state
    OuterReady q full CB (parent + 1) (5 * (start + 32)) after ∧ Frame q full CB state after := by
  let initialized := natRun rom containing 17 state
  obtain ⟨ri, hfi⟩ := row_initialize rom q full CB containing start code parent state ready hp
  let scanned := natRun rom containing (childSteps q full parent (preparedSize q full) + 9) initialized
  obtain ⟨rs, hfs⟩ := child_scan rom q full hq hl CB containing start code parent initialized ri hp
  have hf := row_finish rom q full CB containing start code parent scanned rs hp
  dsimp only at hf
  dsimp only
  rw [show rowSteps q full parent = 17 + ((childSteps q full parent (preparedSize q full) + 9) + 22) by
    unfold rowSteps; omega, natRun_add, natRun_add]
  exact ⟨hf.1, (hfi.trans hfs).trans hf.2⟩

theorem outer_scan_partial (state : NatState)
    (ready : OuterReady q full CB 0 (5 * (start + 32)) state)
    (count : Nat) (hc : count ≤ preparedSize q full) :
    let after := natRun rom containing (outerSteps q full count) state
    OuterReady q full CB count (5 * (start + 32)) after ∧ Frame q full CB state after := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [outerSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show OuterReady q full CB 0 (5 * (start + 32)) state ∧ Frame q full CB state state from
        ⟨ready, Frame.refl _ _ _ state⟩)
  | succ count ih =>
    intro hc
    obtain ⟨rp, hf⟩ := ih (by omega)
    let previous := natRun rom containing (outerSteps q full count) state
    have hr := row_iteration rom q full hq hl CB containing start code count previous rp (by omega)
    dsimp only at hr
    dsimp only
    rw [outerSteps_succ, natRun_add]
    exact ⟨hr.1, hf.trans hr.2⟩

/-- Full actual144 body reaches ACTIVE pc+144 and the exact original
virtual internal-degrees/children cache. Full Word-prefix proof remains
separate; this is not the whole original A19 preprocessor. -/
theorem build (state : NatState) (input : InputData q full CB state)
    (hpc : state.pc = 5 * start) (ha : state.halted = false) :
    let after := natRun rom containing (totalSteps q full) state
    OutputData q full CB after ∧ Frame q full CB state after ∧
      after.pc = 5 * (start + 144) ∧ after.halted = false := by
  let initialized := natRun rom containing 32 state
  obtain ⟨ri, hfi⟩ := initialize_phase rom q full CB containing start code state input hpc ha
  let scanned := natRun rom containing (outerSteps q full (preparedSize q full)) initialized
  obtain ⟨rs, hfs⟩ := outer_scan_partial rom q full hq hl CB containing start code initialized ri (preparedSize q full) le_rfl
  let finished := runOps rom (boundedTest 64 (start + 144)) scanned
  have hp : finished.pc = 5 * (start + 144) := by
    rw [branch_pc rom CB (preparedSize q full) (preparedSize q full) 64 (start + 144) scanned
      rs.controls.input.address rs.controls.size_cell rs.parent_cell, Nat.sub_self, ite_eq_left rfl]
  have hactive : finished.halted = false := (runOps_halted rom _ scanned).trans rs.controls.active
  have hrun : natRun rom containing (totalSteps q full) state = finished := by
    rw [totalSteps, Nat.add_assoc, natRun_add, natRun_add]
    exact chunk_run rom containing start code .outerTest scanned rs.controls.pc rs.controls.active
  have rf := rs.of_heap_eq (show finished.heap = scanned.heap from rfl) rfl hp hactive
  rw [hrun]
  refine ⟨?_, (hfi.trans hfs).trans (show Frame q full CB scanned finished from fun _ _ => rfl), hp, hactive⟩
  refine ⟨rf.controls.input, ?_, ?_⟩
  · intro node
    exact (rf.degrees node.val node.isLt).trans ((exact_lists q full hq hl).1 node)
  · intro position hposition
    have hflat : beforeList q full (preparedSize q full) = (givenTreeROM q full).children := by
      unfold beforeList
      rw [flatPrefix_full]
      exact (exact_lists q full hq hl).2.1
    have h := rf.children position (by rw [hflat]; exact hposition)
    rw [hflat] at h
    exact h

end Linked
end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
