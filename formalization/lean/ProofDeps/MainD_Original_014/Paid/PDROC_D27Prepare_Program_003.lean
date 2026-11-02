module

public import Paid.PDROC_D27Prepare_Program_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

@[expose] public section

namespace PDROC.D27Prepare.Program

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDCompute.Solver
open PDMenu.ComputeFrame

/-- A finite straight-code proof specification. It is not a machine
instruction and cannot evaluate a search, table, or data-dependent loop. -/
inductive SlotCommand where
  | constant (target : ℕ) (value : Cell)
  | copy (source target : ℕ)
  | natural (operation : NatOp) (left right target : ℕ)
  | rational (operation : RatOp) (left right target : ℕ)
  | toRational (source target : ℕ)

structure SlotMemory where
  value : ℕ → Cell
  present : Finset ℕ

def SlotMemory.write (memory : SlotMemory) (target : ℕ) (value : Cell) : SlotMemory :=
  ⟨Function.update memory.value target value,insert target memory.present⟩

structure MemoryMatch (state : State) (memory : SlotMemory) : Prop where
  heap : state.heap=memory.value
  live : state.live=memory.present
  base : state.register .fresh=.natural 0

def SlotCommand.code : SlotCommand → List Instruction
  | .constant target value => constantSlot target value
  | .copy source target => copySlot source target
  | .natural operation left right target => natBinarySlots operation left right target
  | .rational operation left right target => ratBinarySlots operation left right target
  | .toRational source target => natToRatSlot source target

def SlotCommand.eval (command : SlotCommand) (memory : SlotMemory) : Option SlotMemory :=
  match command with
  | .constant target value => some (memory.write target value)
  | .copy source target =>
      if source ∈ memory.present then some (memory.write target (memory.value source)) else none
  | .natural operation left right target =>
      if left ∈ memory.present ∧ right ∈ memory.present then do
        let x ← (memory.value left).nat?
        let y ← (memory.value right).nat?
        let value ← operation.eval x y
        some (memory.write target (.natural value))
      else none
  | .rational operation left right target =>
      if left ∈ memory.present ∧ right ∈ memory.present then do
        let x ← (memory.value left).rat?
        let y ← (memory.value right).rat?
        let value ← operation.eval x y
        some (memory.write target (.rational value))
      else none
  | .toRational source target =>
      if source ∈ memory.present then do
        let value ← (memory.value source).nat?
        some (memory.write target (.rational value))
      else none

theorem MemoryMatch.write_of_fields (before after : State) (memory : SlotMemory)
    (target : ℕ) (value : Cell) (matched : MemoryMatch before memory)
    (heap : after.heap=Function.update before.heap target value)
    (live : after.live=insert target before.live)
    (base : after.register .fresh=before.register .fresh) :
    MemoryMatch after (memory.write target value) := by
  constructor
  · simpa only [SlotMemory.write,matched.heap] using heap
  · simpa only [SlotMemory.write,matched.live] using live
  · exact base.trans matched.base

theorem SlotCommand.code_straight (command : SlotCommand) : StraightCode command.code := by
  cases command with
  | constant target value => exact constantSlot_straight target value
  | copy source target => exact copySlot_straight source target
  | natural operation left right target => exact natBinarySlots_straight operation left right target
  | rational operation left right target => exact ratBinarySlots_straight operation left right target
  | toRational source target => exact natToRatSlot_straight source target

theorem SlotCommand.code_length_le (command : SlotCommand) : command.code.length ≤ 10 := by
  cases command with
  | constant _ _ => change 4 ≤ 10; decide
  | copy _ _ => change 6 ≤ 10; decide
  | natural _ _ _ _ => change 10 ≤ 10; decide
  | rational _ _ _ _ => change 10 ≤ 10; decide
  | toRational _ _ => change 7 ≤ 10; decide

/-- Each specification command refines to actual execution of its literal
4/6/7/10 original instructions, with exact heap/live/output/pc effects. -/
theorem SlotCommand.realize (command : SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (heval : command.eval memory=some next) :
    ∃ after : State, linearExecute input command.code before=some after ∧
      MemoryMatch after next ∧ after.output=before.output ∧
      after.pc=before.pc+command.code.length := by
  cases command with
  | constant target value =>
      have hn : memory.write target value=next := Option.some.inj heval
      subst next
      have fields := constantSlotResult_fields before 0 target value
      refine ⟨constantSlotResult before 0 target value,
        constantSlot_execute input before 0 target value matched.base,?_,fields.2.2.2.2,fields.2.2.2.1⟩
      apply MemoryMatch.write_of_fields before _ memory target value matched
      · simpa only [Nat.zero_add] using fields.1
      · simpa only [Nat.zero_add] using fields.2.1
      · exact fields.2.2.1
  | copy source target =>
      have hs : source ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval,hn] at heval
      have hn : memory.write target (memory.value source)=next := by
        simpa only [SlotCommand.eval,ite_eq_left hs,Option.some.injEq] using heval
      subst next
      have fields := copySlotResult_fields before 0 source target
      refine ⟨copySlotResult before 0 source target,
        copySlot_execute input before 0 source target matched.base (by simpa only [Nat.zero_add,matched.live] using hs),
        ?_,fields.2.2.2.2,fields.2.2.2.1⟩
      apply MemoryMatch.write_of_fields before _ memory target (memory.value source) matched
      · simpa only [Nat.zero_add,matched.heap] using fields.1
      · simpa only [Nat.zero_add] using fields.2.1
      · exact fields.2.2.1
  | natural operation left right target =>
      have hs : left ∈ memory.present ∧ right ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval,hn] at heval
      cases hx : memory.value left with
      | rational x => simp [SlotCommand.eval,hs,hx,Cell.nat?] at heval
      | natural x =>
          cases hy : memory.value right with
          | rational y => simp [SlotCommand.eval,hs,hx,hy,Cell.nat?] at heval
          | natural y =>
              have he : ((operation.eval x y).bind fun value => some (memory.write target (.natural value)))=some next := by
                simpa [SlotCommand.eval,hs,hx,hy,Cell.nat?] using heval
              obtain ⟨value,hop,hn⟩ := Option.bind_eq_some_iff.mp he
              have hn' : memory.write target (.natural value)=next := Option.some.inj hn
              subst next
              have fields := natBinarySlotsResult_fields before 0 left right target value
              refine ⟨natBinarySlotsResult before 0 left right target value,
                natBinarySlots_execute input before 0 left right target operation x y value matched.base
                  (by simpa only [Nat.zero_add,matched.live] using hs.1)
                  (by simpa only [Nat.zero_add,matched.live] using hs.2)
                  (by simpa only [Nat.zero_add,matched.heap] using hx)
                  (by simpa only [Nat.zero_add,matched.heap] using hy) hop,
                ?_,fields.2.2.2.2,fields.2.2.2.1⟩
              apply MemoryMatch.write_of_fields before _ memory target (.natural value) matched
              · simpa only [Nat.zero_add] using fields.1
              · simpa only [Nat.zero_add] using fields.2.1
              · exact fields.2.2.1
  | rational operation left right target =>
      have hs : left ∈ memory.present ∧ right ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval,hn] at heval
      cases hx : memory.value left with
      | natural x => simp [SlotCommand.eval,hs,hx,Cell.rat?] at heval
      | rational x =>
          cases hy : memory.value right with
          | natural y => simp [SlotCommand.eval,hs,hx,hy,Cell.rat?] at heval
          | rational y =>
              have he : ((operation.eval x y).bind fun value => some (memory.write target (.rational value)))=some next := by
                simpa [SlotCommand.eval,hs,hx,hy,Cell.rat?] using heval
              obtain ⟨value,hop,hn⟩ := Option.bind_eq_some_iff.mp he
              have hn' : memory.write target (.rational value)=next := Option.some.inj hn
              subst next
              refine ⟨ratBinarySlotsResult before 0 left right target value,
                ratBinarySlots_execute input before 0 left right target operation x y value matched.base
                  (by simpa only [Nat.zero_add,matched.live] using hs.1)
                  (by simpa only [Nat.zero_add,matched.live] using hs.2)
                  (by simpa only [Nat.zero_add,matched.heap] using hx)
                  (by simpa only [Nat.zero_add,matched.heap] using hy) hop,
                ?_,ratBinarySlotsResult_output ..,ratBinarySlotsResult_pc ..⟩
              apply MemoryMatch.write_of_fields before _ memory target (.rational value) matched
              · simpa only [Nat.zero_add] using (ratBinarySlotsResult_heap before 0 left right target value)
              · simpa only [Nat.zero_add] using (ratBinarySlotsResult_live before 0 left right target value)
              · exact ratBinarySlotsResult_base ..
  | toRational source target =>
      have hs : source ∈ memory.present := by
        by_contra hn
        simp [SlotCommand.eval,hn] at heval
      cases hx : memory.value source with
      | rational x => simp [SlotCommand.eval,hs,hx,Cell.nat?] at heval
      | natural value =>
          have hn : memory.write target (.rational value)=next := by
            simpa [SlotCommand.eval,hs,hx,Cell.nat?] using heval
          subst next
          have fields := natToRatSlotResult_fields before 0 source target value
          refine ⟨natToRatSlotResult before 0 source target value,
            natToRatSlot_execute input before 0 source target value matched.base
              (by simpa only [Nat.zero_add,matched.live] using hs)
              (by simpa only [Nat.zero_add,matched.heap] using hx),
            ?_,fields.2.2.2.2,fields.2.2.2.1⟩
          apply MemoryMatch.write_of_fields before _ memory target (.rational value) matched
          · simpa only [Nat.zero_add] using fields.1
          · simpa only [Nat.zero_add] using fields.2.1
          · exact fields.2.2.1

def slotSequenceCode (commands : List SlotCommand) : List Instruction := commands.flatMap SlotCommand.code

def slotSequenceEval : List SlotCommand → SlotMemory → Option SlotMemory
  | [],memory => some memory
  | command::rest,memory => (command.eval memory).bind (slotSequenceEval rest)

theorem slotSequence_straight (commands : List SlotCommand) : StraightCode (slotSequenceCode commands) := by
  intro instruction member
  obtain ⟨command,hcommand,hinstruction⟩ := List.mem_flatMap.mp member
  exact command.code_straight instruction hinstruction

theorem slotSequence_length_le (commands : List SlotCommand) :
    (slotSequenceCode commands).length ≤ 10*commands.length := by
  induction commands with
  | nil => simp [slotSequenceCode]
  | cons command rest ih =>
      simp only [slotSequenceCode,List.flatMap_cons,List.length_append,List.length_cons]
      have hc := command.code_length_le
      change (slotSequenceCode rest).length ≤ 10*rest.length at ih
      change command.code.length+(slotSequenceCode rest).length ≤ _
      omega

theorem slotSequence_realize (commands : List SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (heval : slotSequenceEval commands memory=some next) :
    ∃ after : State, linearExecute input (slotSequenceCode commands) before=some after ∧
      MemoryMatch after next ∧ after.output=before.output ∧
      after.pc=before.pc+(slotSequenceCode commands).length := by
  induction commands generalizing before memory with
  | nil =>
      have hn : memory=next := Option.some.inj heval
      subst next
      exact ⟨before,rfl,matched,rfl,by simp [slotSequenceCode]⟩
  | cons command rest ih =>
      obtain ⟨middleMemory,hfirst,hrest⟩ := Option.bind_eq_some_iff.mp heval
      obtain ⟨middle,hcode,hmatch,houtput,hpc⟩ := command.realize input before memory middleMemory matched hfirst
      obtain ⟨after,hrestcode,hafter,hafteroutput,hafterpc⟩ := ih middle middleMemory hmatch hrest
      refine ⟨after,?_,hafter,hafteroutput.trans houtput,?_⟩
      · simpa only [slotSequenceCode,List.flatMap_cons,PDLower.CalibrationCompute.linearExecute_append,
          hcode,Option.bind_some] using hrestcode
      · simp only [slotSequenceCode,List.flatMap_cons,List.length_append] at hafterpc ⊢
        omega

/-- Compiled finite specification, actual fixed-program fetch, genuine
trace, and every actual strict-prefix state. No loop semantics is assumed. -/
theorem slotSequence_trace (commands : List SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (heval : slotSequenceEval commands memory=some next)
    (fetch : FetchesCode program before.pc (slotSequenceCode commands)) :
    ∃ (after : State) (trace : List State), MemoryMatch after next ∧ after.output=before.output ∧
      after.pc=before.pc+(slotSequenceCode commands).length ∧
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*((slotSequenceCode commands).length+1) ∧
      ∀ state ∈ trace.dropLast, ∃ count < (slotSequenceCode commands).length,
        linearExecute input ((slotSequenceCode commands).take count) before=some state := by
  obtain ⟨after,execute,matchAfter,outputAfter,pcAfter⟩ := slotSequence_realize commands input before memory next matched heval
  obtain ⟨trace,head,last,chain,bound,prefixStates⟩ :=
    literal_fragment_trace input (slotSequenceCode commands) (slotSequence_straight commands) before after fetch execute
  exact ⟨after,trace,matchAfter,outputAfter,pcAfter,head,last,chain,bound,prefixStates⟩


/-- The length-exact actual straight fragment, independent of slot semantics. -/
theorem literal_fragment_trace_length (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before after : State)
    (fetch : FetchesCode program before.pc code)
    (execute : linearExecute input code before=some after) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=code.length+1 ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      ∀ state ∈ trace.dropLast, ∃ count < code.length,
        linearExecute input (code.take count) before=some state :=
  linearExecute_trace program input code straight before after fetch execute

/-- Append exactly one actual control step. The explicit body trace and
its strict-prefix execution witnesses remain available for all-prefix bounds. -/
theorem literal_control_trace (input : List Cell) (code : List Instruction)
    (straight : StraightCode code) (before middle after : State)
    (fetch : FetchesCode program before.pc code)
    (execute : linearExecute input code before=some middle)
    (controlStep : step program input middle=some after) :
    ∃ (bodyTrace wholeTrace : List State), wholeTrace=bodyTrace++[after] ∧
      bodyTrace.head?=some before ∧ bodyTrace.getLast?=some middle ∧
      bodyTrace.length=code.length+1 ∧
      bodyTrace.IsChain (fun first later => step program input first=some later) ∧
      (∀ state ∈ bodyTrace.dropLast, ∃ count < code.length,
        linearExecute input (code.take count) before=some state) ∧
      wholeTrace.head?=some before ∧ wholeTrace.getLast?=some after ∧
      wholeTrace.length=code.length+2 ∧
      wholeTrace.IsChain (fun first later => step program input first=some later) ∧
      time program wholeTrace ≤ 15*(code.length+2) ∧
      ∀ state ∈ wholeTrace, state ∈ bodyTrace ∨ state=after := by
  obtain ⟨body,head,last,length,chain,prefixStates⟩ :=
    literal_fragment_trace_length input code straight before middle fetch execute
  obtain ⟨wholeChain,_⟩ := chain_append_control program input body middle after chain last controlStep
  refine ⟨body,body++[after],rfl,head,last,length,chain,prefixStates,?_,?_,?_,wholeChain,?_,?_⟩
  · cases body with
    | nil => simp at head
    | cons first rest => simpa using head
  · simp
  · simp only [List.length_append,List.length_singleton,length,Nat.add_assoc]
  · have bound := time_le_length program (body++[after])
    simpa only [List.length_append,List.length_singleton,length,Nat.add_assoc] using bound
  · intro state member
    simpa only [List.mem_append,List.mem_singleton] using member

/-- Length-exact companion, retaining the same actual strict-prefix witnesses. -/
theorem slotSequence_trace_length (commands : List SlotCommand) (input : List Cell) (before : State)
    (memory next : SlotMemory) (matched : MemoryMatch before memory)
    (heval : slotSequenceEval commands memory=some next)
    (fetch : FetchesCode program before.pc (slotSequenceCode commands)) :
    ∃ (after : State) (trace : List State), MemoryMatch after next ∧ after.output=before.output ∧
      after.pc=before.pc+(slotSequenceCode commands).length ∧
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=(slotSequenceCode commands).length+1 ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*((slotSequenceCode commands).length+1) ∧
      ∀ state ∈ trace.dropLast, ∃ count < (slotSequenceCode commands).length,
        linearExecute input ((slotSequenceCode commands).take count) before=some state := by
  obtain ⟨after,execute,matchAfter,outputAfter,pcAfter⟩ := slotSequence_realize commands input before memory next matched heval
  obtain ⟨trace,head,last,length,chain,prefixStates⟩ :=
    linearExecute_trace program input (slotSequenceCode commands) (slotSequence_straight commands) before after fetch execute
  refine ⟨after,trace,matchAfter,outputAfter,pcAfter,head,last,length,chain,?_,prefixStates⟩
  simpa only [length] using time_le_length program trace

def majoritySetupCommands : List SlotCommand :=
  [.toRational 0 22,
    .rational .multiply 2 2 24,
    .rational .multiply 20 24 32,
    .rational .subtract 17 32 25,
    .rational .multiply 25 25 26,
    .rational .multiply 18 22 32,
    .rational .divide 3 32 33,
    .rational .multiply 33 33 27,
    .copy 25 28]

theorem majoritySetup_compiled : slotSequenceCode majoritySetupCommands=majoritySetup := rfl

def majorityStepCommands : List SlotCommand :=
  [.natural .add 6 15 6,
    .rational .multiply 28 26 28]

theorem majorityStep_compiled : slotSequenceCode majorityStepCommands=majorityStep := rfl

def endpointSetupCommands : List SlotCommand :=
  [.toRational 6 23,
    .rational .multiply 20 22 32,
    .rational .multiply 32 23 32,
    .rational .divide 3 32 29,
    .rational .multiply 18 2 32,
    .rational .add 17 32 33,
    .rational .subtract 17 32 34,
    .rational .divide 33 34 30,
    .copy 17 28]

theorem endpointSetup_compiled : slotSequenceCode endpointSetupCommands=endpointSetup := rfl

def endpointStepCommands : List SlotCommand :=
  [.natural .add 7 14 7,
    .rational .multiply 28 30 28]

theorem endpointStep_compiled : slotSequenceCode endpointStepCommands=endpointStep := rfl

def exponentSetupCommands : List SlotCommand :=
  [.rational .divide 29 19 32,
    .rational .multiply 2 32 31,
    .copy 21 28]

theorem exponentSetup_compiled : slotSequenceCode exponentSetupCommands=exponentSetup := rfl

def exponentStepCommands : List SlotCommand :=
  [.natural .add 8 14 8,
    .rational .multiply 28 21 28]

theorem exponentStep_compiled : slotSequenceCode exponentStepCommands=exponentStep := rfl

def firstCeilSetupCommands : List SlotCommand :=
  [.toRational 7 32,
    .rational .add 32 17 32,
    .rational .divide 32 2 32]

theorem firstCeilSetup_compiled : slotSequenceCode firstCeilSetupCommands=firstCeilSetup := rfl

def secondCeilSetupCommands : List SlotCommand :=
  [.toRational 8 32,
    .rational .multiply 18 32 32,
    .rational .divide 32 24 32]

theorem secondCeilSetup_compiled : slotSequenceCode secondCeilSetupCommands=secondCeilSetup := rfl

def multiplierSetupCommands : List SlotCommand :=
  [.rational .multiply 20 4 32,
    .rational .multiply 32 22 32,
    .rational .multiply 32 23 32,
    .rational .divide 32 3 11,
    .copy 13 35,
    .copy 17 39]

theorem multiplierSetup_compiled : slotSequenceCode multiplierSetupCommands=multiplierSetup := rfl

def dyadicStepCommands : List SlotCommand :=
  [.natural .add 35 14 35,
    .rational .multiply 39 21 39]

theorem dyadicStep_compiled : slotSequenceCode dyadicStepCommands=dyadicStep := rfl

def binomialSetupCommands : List SlotCommand :=
  [.copy 13 40,
    .copy 17 41,
    .copy 16 42]

theorem binomialSetup_compiled : slotSequenceCode binomialSetupCommands=binomialSetup := rfl

def binomialStepCommands : List SlotCommand :=
  [.natural .subtract 0 40 48,
    .natural .add 40 14 49,
    .toRational 48 32,
    .toRational 49 33,
    .rational .divide 32 33 50,
    .rational .multiply 41 50 41,
    .copy 49 40]

theorem binomialStep_compiled : slotSequenceCode binomialStepCommands=binomialStep := rfl

def budgetRatioSetupCommands : List SlotCommand :=
  [.rational .multiply 18 11 32,
    .rational .multiply 32 3 32,
    .rational .divide 32 44 45]

theorem budgetRatioSetup_compiled : slotSequenceCode budgetRatioSetupCommands=budgetRatioSetup := rfl

def budgetHalveSetupCommands : List SlotCommand :=
  [.natural .subtract 46 14 47,
    .copy 13 10]

theorem budgetHalveSetup_compiled : slotSequenceCode budgetHalveSetupCommands=budgetHalveSetup := rfl

def budgetHalveStepCommands : List SlotCommand :=
  [.natural .divide 47 15 47,
    .natural .add 10 14 10]

theorem budgetHalveStep_compiled : slotSequenceCode budgetHalveStepCommands=budgetHalveStep := rfl

end PDROC.D27Prepare.Program
