module

public import Paid.PDCompute_SolverSequenceMemory_051
public import Paid.PDMenu_ComputeFrame_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

namespace PDLower.CoreSearch

/-- Search scalar scripts preserve prepared0..12, output-loop43..45 and
retained-copy46/47, including at every intermediate ISA instruction. -/
def scalarRegion : Finset ℕ := Finset.Icc 13 42

def commandTarget : HeaderCommand → ℕ
  | .constant target _ => target
  | .copy _ target => target
  | .rational _ _ _ target => target

theorem scalarRegion_outside (address : ℕ) (outside : address<13∨42<address) : address∉scalarRegion := by
  simp only [scalarRegion,Finset.mem_Icc]
  omega

private theorem unchanged_frame (before after : State) (heap : after.heap=before.heap) (live : after.live=before.live) :
    MemoryFrame scalarRegion before after :=
  ⟨fun address _ => congrFun heap address,fun address _ => by rw [live]⟩

private theorem update_frame (before after : State) (target : ℕ) (value : Cell)
    (inside : target∈scalarRegion) (heap : after.heap=Function.update before.heap target value)
    (live : after.live=before.live) : MemoryFrame scalarRegion before after := by
  refine ⟨?_,fun address _ => by rw [live]⟩
  intro address outside
  have different : address≠target := by intro equal;exact outside (equal.symm ▸ inside)
  rw [heap]
  exact Function.update_of_ne different _ _

/-- Refine the frozen Header48 result to the actual targets13..42.
This uses the original macro prefixes; Header48 alone would permit writes
to prepared input and retained-copy cells and is insufficient here. -/
theorem command_prefix_scalar_memory (command : HeaderCommand) (input : List Cell) (before after : State)
    (values next : ℕ→Cell) (valid : command.Valid) (target : commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : command.eval values=some next) (count : ℕ) (bounded : count≤command.code.length)
    (executed : linearExecute input (command.code.take count) before=some after) :
    MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0 := by
  have broad := command.prefix_memory input before after 0 values next valid header fresh evaluated count bounded executed
  refine ⟨?_,broad⟩
  cases command with
  | constant slot value =>
    by_cases short : count<4
    · have old := constantSlot_prefix_memory input before after 0 slot value fresh count short executed
      exact unchanged_frame before after old.1 old.2.1
    · have exactCount : count=4 := by change count≤4 at bounded;omega
      subst count
      have full : linearExecute input (constantSlot slot value) before=some after := executed
      rw [constantSlot_execute input before 0 slot value fresh] at full
      have equal := Option.some.inj full
      subst after
      have fields := constantSlotResult_fields before 0 slot value
      exact update_frame before _ slot value target (by simpa only [Nat.zero_add] using fields.1) broad.2.1
  | copy source slot =>
    by_cases short : count<6
    · have old := copySlot_prefix_memory input before after 0 source slot fresh (header.live source valid.1) count short executed
      exact unchanged_frame before after old.1 old.2.1
    · have exactCount : count=6 := by change count≤6 at bounded;omega
      subst count
      have full : linearExecute input (copySlot source slot) before=some after := executed
      rw [copySlot_execute input before 0 source slot fresh (header.live source valid.1)] at full
      have equal := Option.some.inj full
      subst after
      have fields := copySlotResult_fields before 0 source slot
      exact update_frame before _ slot (before.heap (0+source)) target
        (by simpa only [Nat.zero_add] using fields.1) broad.2.1
  | rational operation left right slot =>
    cases hx : values left with
    | natural x => simp [HeaderCommand.eval,hx,Cell.rat?] at evaluated
    | rational x =>
      cases hy : values right with
      | natural y => simp [HeaderCommand.eval,hx,hy,Cell.rat?] at evaluated
      | rational y =>
        have actual : ((operation.eval x y).bind fun value =>
            some (Function.update values slot (.rational value)))=some next := by
          simpa [HeaderCommand.eval,hx,hy,Cell.rat?] using evaluated
        obtain ⟨value,operationRun,_⟩ := Option.bind_eq_some_iff.mp actual
        have leftValue := (header.value left valid.1).trans hx
        have rightValue := (header.value right valid.2.1).trans hy
        by_cases short : count<10
        · have old := ratBinarySlots_prefix_memory input before after 0 left right slot operation x y value
            fresh (header.live left valid.1) (header.live right valid.2.1) leftValue rightValue operationRun count short executed
          exact unchanged_frame before after old.1 old.2.1
        · have exactCount : count=10 := by change count≤10 at bounded;omega
          subst count
          have full : linearExecute input (ratBinarySlots operation left right slot) before=some after := executed
          rw [ratBinarySlots_execute input before 0 left right slot operation x y value fresh
            (header.live left valid.1) (header.live right valid.2.1) leftValue rightValue operationRun] at full
          have equal := Option.some.inj full
          subst after
          exact update_frame before _ slot (.rational value) target
            (by simpa only [Nat.zero_add] using ratBinarySlotsResult_heap before 0 left right slot value) broad.2.1

theorem commands_prefix_scalar_memory (commands : List HeaderCommand) (input : List Cell) (before after : State)
    (values next : ℕ→Cell) (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next) (count : ℕ) (bounded : count≤(headerCode commands).length)
    (executed : linearExecute input ((headerCode commands).take count) before=some after) :
    MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0 := by
  induction commands generalizing before values count with
  | nil =>
    have same : before=after := by
      simpa only [headerCode,List.flatMap_nil,List.take_nil,linearExecute,Option.some.injEq] using executed
    subst after
    exact ⟨MemoryFrame.refl _ _,HeaderMemory.refl _ _⟩
  | cons command commands ih =>
    obtain ⟨middleValues,firstEval,laterEval⟩ := Option.bind_eq_some_iff.mp evaluated
    have firstValid := valid command (by simp)
    have firstTarget := targets command (by simp)
    by_cases short : count≤command.code.length
    · have takeEq : (headerCode (command::commands)).take count=command.code.take count := List.take_append_of_le_length short
      rw [takeEq] at executed
      exact command_prefix_scalar_memory command input before after values middleValues firstValid firstTarget header fresh firstEval count short executed
    · obtain ⟨middle,firstRun,middleHeader,middleFresh,_pc,_frame,_output⟩ :=
        command.realize input before 0 0 0 values middleValues firstValid header fresh firstEval
      have takeEq : (headerCode (command::commands)).take count=command.code++(headerCode commands).take (count-command.code.length) := by
        change (command.code++headerCode commands).take count=_
        rw [List.take_append,List.take_of_length_le (by omega : command.code.length≤count)]
      rw [takeEq,linearExecute_append,firstRun,Option.bind_some] at executed
      have tailBound : count-command.code.length≤(headerCode commands).length := by
        change count≤(command.code++headerCode commands).length at bounded
        rw [List.length_append] at bounded
        omega
      have firstMemory := command_prefix_scalar_memory command input before middle values middleValues firstValid firstTarget header fresh firstEval
        command.code.length (le_refl _) (by simpa only [List.take_length] using firstRun)
      have laterMemory := ih middle middleValues (fun c member => valid c (by simp only [List.mem_cons];exact Or.inr member))
        (fun c member => targets c (by simp only [List.mem_cons];exact Or.inr member)) middleHeader middleFresh laterEval
        (count-command.code.length) tailBound executed
      exact ⟨firstMemory.1.trans laterMemory.1,firstMemory.2.trans laterMemory.2⟩

theorem commands_trace_scalar (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (values next : ℕ→Cell) (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next) (fetched : FetchesCode program before.pc (headerCode commands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤15*((headerCode commands).length+1) ∧
      linearExecute input (headerCode commands) before=some after ∧
      Header after 0 next ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+(headerCode commands).length ∧
      after.output=before.output ∧ ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  obtain ⟨after,run,afterHeader,afterFresh,pc,_frame,output⟩ :=
    headerCode_realize commands input before 0 0 0 values next valid header fresh evaluated
  obtain ⟨trace,head,last,chain,cost,prefixes⟩ := linearExecute_trace_time program input (headerCode commands)
    (headerCode_straight commands) before after fetched run
  refine ⟨trace,after,head,last,chain,cost,run,afterHeader,afterFresh,pc,output,?_⟩
  intro state member
  have split := List.dropLast_append_getLast? after (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|finalState
  · obtain ⟨count,bound,execute⟩ := prefixes state proper
    exact commands_prefix_scalar_memory commands input before state values next valid targets header fresh evaluated count bound.le execute
  · have same := List.mem_singleton.mp finalState
    subst state
    exact commands_prefix_scalar_memory commands input before after values next valid targets header fresh evaluated
      (headerCode commands).length (le_refl _) (by simpa only [List.take_length] using run)

end PDLower.CoreSearch
