module

public import Paid.PDROC_BitVM_Log_HeapLoad_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.HeapLoad

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Thin original-instruction adapters. The successful source step determines
its own real Nat address and live Cell; they are conclusions, not additional
input fields, machine state or an external numerical/success oracle. -/

theorem load_step_refinement (input : List Cell) (ram next : RAMState) (events : List HeapEvent)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (refines : Refines events ram)
    (executed : Instruction.execute input (.load destination pointer) ram = some next) :
    ∃ (query : ℕ) (value : Cell) (run : List State) (after : State),
      ram.register pointer = .natural query ∧ lookup events query = some value ∧ next = ramLoaded ram destination value ∧
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = true ∧
      Refines events next ∧ RegistersRepresent next after ∧ after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → index ≠ registerSlot destination →
        after.stk index = before.stk index) ∧
      run.length ≤ foundBudget events query destination value before.stk := by
  cases pointerValue : ram.register pointer with
  | rational value => simp [Instruction.execute, pointerValue, Cell.nat?] at executed
  | natural query =>
    have actual := Lookup.execute_load_from_history input events ram destination pointer query refines pointerValue
    rw [executed] at actual
    cases answer : lookup events query with
    | none => simp only [answer, Option.map_none, reduceCtorEq] at actual
    | some value =>
      have nextValue : next = ramLoaded ram destination value := by
        simpa only [answer, Option.map_some, ramLoaded, Option.some.injEq] using actual
      subst next
      obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, heapRefines, registers, currentHistory, frame, length⟩ :=
        load_found_refinement input ram events pointer destination query value before position represented history refines pointerValue answer
      exact ⟨query, value, run, after, rfl, answer, rfl, head, chain, last, halt,
        done, flag, heapRefines, registers, currentHistory, frame, length⟩

theorem load_failure_refinement (input : List Cell) (ram : RAMState) (events : List HeapEvent)
    (pointer destination : Register) (before : State)
    (position : before.l = some startLabel) (represented : RegistersRepresent ram before)
    (history : before.stk 21 = encodeHistory events) (refines : Refines events ram)
    (executed : Instruction.execute input (.load destination pointer) ram = none) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program pointer destination) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program pointer destination) after = none ∧
      after.l = none ∧ Query.equality after.var.2.1 = false ∧ RegistersRepresent ram after ∧
      after.stk 21 = encodeHistory events ∧
      (∀ index : Stack, (index.val < 24 ∨ 30 ≤ index.val) → after.stk index = before.stk index) ∧
      run.length ≤ queryBudget events ((ram.register pointer).nat?.getD 0) before.stk + 2 := by
  cases pointerValue : ram.register pointer with
  | rational value =>
    obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, currentHistory, frame, length⟩ :=
      load_rational_refinement input ram events pointer destination value before position represented history pointerValue
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, currentHistory, frame, ?_⟩
    simp only [Cell.nat?, Option.getD_none, queryBudget]
    omega
  | natural query =>
    have actual := Lookup.execute_load_from_history input events ram destination pointer query refines pointerValue
    rw [executed] at actual
    have missing : lookup events query = none := by
      cases answer : lookup events query with
      | none => rfl
      | some value => simp only [answer, Option.map_some, reduceCtorEq] at actual
    obtain ⟨run, after, head, chain, last, halt, done, flag, sourceExecute, registers, currentHistory, frame, length⟩ :=
      load_missing_refinement input ram events pointer destination query before position represented history refines pointerValue missing
    refine ⟨run, after, head, chain, last, halt, done, flag, registers, currentHistory, frame, ?_⟩
    simpa only [pointerValue, Cell.nat?, Option.getD_some] using length

end PDROC.BitVM.Log.HeapLoad
