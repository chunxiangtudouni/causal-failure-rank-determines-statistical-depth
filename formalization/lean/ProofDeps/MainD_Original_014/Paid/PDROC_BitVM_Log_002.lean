module

public import Paid.PDROC_BitVM_Log_001
public import Mathlib.Data.List.Chain

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Exact source-ISA history refinement. This file remains a specification
component, not a Boolean VM implementation or a heap lookup transition. -/

namespace PDROC.BitVM.Log

open PaperProofs.Paid.Computation

theorem execute_refines (input : List Cell) (instruction : Instruction)
    (events : List HeapEvent) (before after : State)
    (refines : Refines events before)
    (executed : instruction.execute input before = some after) :
    Refines (events ++ (eventOf instruction before).toList) after := by
  cases instruction with
  | store pointer source =>
    cases pointerValue : (before.register pointer).nat? with
    | none => simp [Instruction.execute, pointerValue] at executed
    | some address =>
      simp [Instruction.execute, pointerValue] at executed
      subst after
      simp only [eventOf, pointerValue, Option.map_some, Option.toList_some]
      exact refines.store address (before.register source)
  | release pointer =>
    cases pointerValue : (before.register pointer).nat? with
    | none => simp [Instruction.execute, pointerValue] at executed
    | some address =>
      simp [Instruction.execute, pointerValue] at executed
      subst after
      simp only [eventOf, pointerValue, Option.map_some, Option.toList_some]
      exact refines.release address
  | constant target value | move target source | loadInput target pointer
  | load target pointer | natOp operation target left right
  | ratOp operation target left right | natCompare comparison target left right
  | ratCompare comparison target left right | natToRat target source
  | numeratorAbs target source | denominator target source | negative target source
  | branchZero test yes no | jump destination | jumpIndirect source | output source
  | halt =>
    simp only [eventOf, Option.toList_none, List.append_nil]
    apply refines.carry
    all_goals
      simp only [Instruction.execute, State.set, Option.bind_eq_bind,
        Option.bind_eq_some_iff] at executed
      grind

def stepEvents (program : Array Instruction) (before : State) : List HeapEvent :=
  ((program[before.pc]?).bind (fun instruction => eventOf instruction before)).toList

theorem stepEvents_length (program : Array Instruction) (before : State) :
    (stepEvents program before).length ≤ 1 := by
  unfold stepEvents
  cases (program[before.pc]?).bind (fun instruction => eventOf instruction before) <;> simp

theorem step_refines (program : Array Instruction) (input : List Cell)
    (events : List HeapEvent) (before after : State)
    (refines : Refines events before)
    (executed : step program input before = some after) :
    Refines (events ++ stepEvents program before) after := by
  simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at executed
  obtain ⟨instruction, fetched, executed⟩ := executed
  simpa only [stepEvents, fetched, Option.bind_some] using
    execute_refines input instruction events before after refines executed

/-- A real source chain adds at most one event per transition, including failed
loads only when they actually step. It starts from the actual empty heap. -/
theorem chain_history (program : Array Instruction) (input : List Cell)
    (before : State) (rest : List State) (events : List HeapEvent)
    (chain : (before :: rest).IsChain (fun a b => step program input a = some b))
    (refines : Refines events before) :
    ∃ finalEvents, Refines finalEvents ((before :: rest).getLast (by simp)) ∧
      finalEvents.length ≤ events.length + rest.length := by
  induction rest generalizing before events with
  | nil => exact ⟨events, refines, by simp⟩
  | cons middle rest ih =>
    have first := (List.isChain_cons_cons.mp chain).1
    obtain ⟨finalEvents, finalRefines, size⟩ := ih middle
      (events ++ stepEvents program before) chain.tail
      (step_refines program input events before middle refines first)
    refine ⟨finalEvents, ?_, ?_⟩
    · simpa only [List.getLast_cons_cons] using finalRefines
    · have one := stepEvents_length program before
      simp only [List.length_append] at size
      simp only [List.length_cons]
      omega

theorem initial_chain_history (program : Array Instruction) (input : List Cell)
    (rest : List State)
    (chain : (initial :: rest).IsChain (fun a b => step program input a = some b)) :
    ∃ events, Refines events ((initial :: rest).getLast (by simp)) ∧
      events.length ≤ rest.length := by
  simpa only [List.length_nil, zero_add] using
    chain_history program input initial rest [] chain initial_refines

end PDROC.BitVM.Log
