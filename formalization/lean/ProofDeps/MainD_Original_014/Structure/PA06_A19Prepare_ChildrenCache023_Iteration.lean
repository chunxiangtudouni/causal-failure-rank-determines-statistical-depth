module

public import Structure.PA06_A19Prepare_ChildrenCache023_State

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled actual parent/child iteration of the fixed144-op
cache builder. The branch uses the real cached encoded-parent read. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix

def bitHeap (q : Nat) (full : List (Finset (Fin q))) (CB parent child : Nat) (state : NatState) : Nat → Nat :=
  if parentWord q full child = parent + 1 then
    Function.update (Function.update (Function.update (Function.update state.heap
      (childrenBase CB (mass q full) (preparedSize q full) + state.heap (CB + 66)) child)
        (CB + 69) (state.heap (CB + 69) + 1)) (CB + 66) (state.heap (CB + 66) + 1)) (CB + 65) (child + 1)
  else Function.update state.heap (CB + 65) (child + 1)

/-- One true fetched iteration. Internal degree/child lists are not used
as answers: the machine reads the cached parent and compares parent+1. -/
theorem child_iteration_raw (rom : PhysicalROM) (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (parent child : Nat) (state : NatState)
    (ready : InnerReady q full CB parent child (5 * (start + 49)) state)
    (hc : child < preparedSize q full) :
    let after := natRun rom containing (iterationSteps (parentWord q full) parent child) state
    after.heap = bitHeap q full CB parent child state ∧ after.register .address = CB ∧
      after.pc = 5 * (start + 49) ∧ after.halted = false := by
  let tested := runOps rom (boundedTest 65 (start + 122)) state
  have htHeap : tested.heap = state.heap := rfl
  have htCB : tested.register .address = CB := ready.controls.input.address
  have htActive : tested.halted = false := (runOps_halted rom _ state).trans ready.controls.active
  have htPC : tested.pc = 5 * (start + 58) := by
    rw [branch_pc rom CB (preparedSize q full) child 65 (start + 122) state
      ready.controls.input.address ready.controls.size_cell ready.child_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hc), ready.controls.pc]
    omega
  let compared := runOps rom (matchTest start) tested
  have hmHeap : compared.heap = state.heap := rfl
  have hmCB : compared.register .address = CB := ready.controls.input.address
  have hmActive : compared.halted = false := (runOps_halted rom _ tested).trans htActive
  have hmPC : compared.pc = if parentWord q full child = parent + 1 then
      5 * (start + 84) else 5 * (start + 81) := by
    have h := match_pc rom CB (mass q full) parent child start tested htCB
      (by rw [htHeap]; exact ready.controls.input.mass_cell)
      (by rw [htHeap]; exact ready.parent_cell) (by rw [htHeap]; exact ready.child_cell)
    rw [htHeap, ready.controls.input.parents child hc, htPC] at h
    dsimp only [compared]
    rw [h]
    split_ifs <;> omega
  have htRun := chunk_run rom containing start code .innerTest state ready.controls.pc ready.controls.active
  have hmRun := chunk_run rom containing start code .matchTest tested htPC htActive
  change natRun rom containing 9 state = tested at htRun
  change natRun rom containing 23 tested = compared at hmRun
  by_cases heq : parentWord q full child = parent + 1
  · have hmTarget : compared.pc = 5 * (start + 84) := by simpa only [heq, ite_true] using hmPC
    let written := runOps rom matched compared
    have hwCB : written.register .address = CB := ready.controls.input.address
    have hwActive : written.halted = false := (runOps_halted rom _ compared).trans hmActive
    have hwPC : written.pc = 5 * (start + 111) := by
      rw [runOps_pc rom _ compared (by
        simp [matched, writeChild, incrementRel, loadRel, storeRel, NoJump]), matched_length, hmTarget]
      omega
    have hp : CB + 71 ≤ compared.heap (CB + 68) := by
      rw [hmHeap, ready.controls.children_base]
      unfold childrenBase degreeBase
      omega
    have hwHeap := matched_heap rom CB compared hmCB hp
    rw [hmHeap, ready.controls.children_base, ready.child_cell] at hwHeap
    let finished := runOps rom (innerTail start) written
    have hfHeap : finished.heap = bitHeap q full CB parent child state := by
      rw [show finished = runOps _ _ _ from rfl, innerTail_heap, hwCB, hwHeap]
      simp (disch := omega) [bitHeap, heq, childrenBase, degreeBase, ready.child_cell]
    have hfPC : finished.pc = 5 * (start + 49) := innerTail_pc rom start written
    have hfActive : finished.halted = false := (runOps_halted rom _ written).trans hwActive
    have hfCB : finished.register .address = CB := hwCB
    have hwRun := chunk_run rom containing start code .matched compared hmTarget hmActive
    have hfRun := chunk_run rom containing start code .innerTail written hwPC hwActive
    change natRun rom containing 27 compared = written at hwRun
    change natRun rom containing 11 written = finished at hfRun
    have hrun : natRun rom containing 70 state = finished := by
      rw [show 70 = 9 + (23 + (27 + 11)) from rfl, natRun_add, htRun, natRun_add, hmRun,
        natRun_add, hwRun, hfRun]
    simp only [iterationSteps, heq, ite_true]
    rw [hrun]
    exact ⟨hfHeap, hfCB, hfPC, hfActive⟩
  · have hmTarget : compared.pc = 5 * (start + 81) := by simpa only [heq, ite_false] using hmPC
    let skipped := runOps rom (jumpTo (start + 111)) compared
    have hsHeap : skipped.heap = state.heap := rfl
    have hsCB : skipped.register .address = CB := ready.controls.input.address
    have hsPC : skipped.pc = 5 * (start + 111) := by
      simp [skipped, jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
    have hsActive : skipped.halted = false := (runOps_halted rom _ compared).trans hmActive
    let finished := runOps rom (innerTail start) skipped
    have hfHeap : finished.heap = bitHeap q full CB parent child state := by
      rw [show finished = runOps _ _ _ from rfl, innerTail_heap, hsCB, hsHeap, ready.child_cell]
      simp only [bitHeap, heq, ite_false]
    have hfCB : finished.register .address = CB := hsCB
    have hfPC : finished.pc = 5 * (start + 49) := innerTail_pc rom start skipped
    have hfActive : finished.halted = false := (runOps_halted rom _ skipped).trans hsActive
    have hsRun := chunk_run rom containing start code .skip compared hmTarget hmActive
    have hfRun := chunk_run rom containing start code .innerTail skipped hsPC hsActive
    change natRun rom containing 3 compared = skipped at hsRun
    change natRun rom containing 11 skipped = finished at hfRun
    have hrun : natRun rom containing 46 state = finished := by
      rw [show 46 = 9 + (23 + (3 + 11)) from rfl, natRun_add, htRun, natRun_add, hmRun,
        natRun_add, hsRun, hfRun]
    simp only [iterationSteps, heq, ite_false]
    rw [hrun]
    exact ⟨hfHeap, hfCB, hfPC, hfActive⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
