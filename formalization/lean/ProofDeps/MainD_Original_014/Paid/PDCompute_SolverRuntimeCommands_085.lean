module

public import Paid.PDCompute_SolverNatSlots_084

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

/-- A code-generation notation mixing the existing scalar expansion
with actual typed natural arithmetic. Every command expands to at most
ten original ISA instructions. No constructor is a machine primitive. -/
inductive RuntimeCommand where
  | scalar (command : HeaderCommand)
  | natural (operation : NatOp) (left right target : ℕ)

def RuntimeCommand.code : RuntimeCommand → List Instruction
  | .scalar command => command.code
  | .natural operation left right target => natBinarySlots operation left right target

def RuntimeCommand.Valid : RuntimeCommand → Prop
  | .scalar command => command.Valid
  | .natural _ left right target => left < headerWords ∧ right < headerWords ∧ target < headerWords

def RuntimeCommand.eval (command : RuntimeCommand) (values : ℕ → Cell) : Option (ℕ → Cell) := do
  match command with
  | .scalar command => command.eval values
  | .natural operation left right target =>
    let x ← (values left).nat?
    let y ← (values right).nat?
    let value ← operation.eval x y
    pure (Function.update values target (.natural value))

theorem RuntimeCommand.code_length_le (command : RuntimeCommand) : command.code.length ≤ 10 := by
  cases command with
  | scalar command => exact HeaderCommand.code_length_le command
  | natural operation left right target => exact le_refl _

theorem RuntimeCommand.trace_memory (command : RuntimeCommand) (program : Program) (input : List Cell)
    (before : State) (base n k : ℕ) (values next : ℕ → Cell)
    (valid : command.Valid) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (heval : command.eval values=some next)
    (fetch : FetchesCode program before.pc command.code) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 330 ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+command.code.length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  cases command with
  | scalar command =>
    have scalarEval : command.eval values=some next := heval
    have evaluation : headerEval [command] values=some next := by
      simp only [headerEval,scalarEval,Option.bind_some]
    have fetching : FetchesCode program before.pc (headerCode [command]) := by
      simpa only [headerCode,List.flatMap_cons,List.flatMap_nil,List.append_nil,RuntimeCommand.code] using fetch
    have allValid : ∀ item ∈ [command],item.Valid := by
      intro item member
      have same : item=command := by simpa only [List.mem_singleton] using member
      subst item
      exact valid
    simpa only [List.length_singleton,headerCode,List.flatMap_cons,List.flatMap_nil,List.append_nil,RuntimeCommand.code] using
      headerCode_trace_memory [command] program input before base n k values next allValid header hbase evaluation fetching
  | natural operation left right target =>
    cases hx : values left with
    | rational x => simp [RuntimeCommand.eval,hx,Cell.nat?] at heval
    | natural x =>
      cases hy : values right with
      | rational y => simp [RuntimeCommand.eval,hx,hy,Cell.nat?] at heval
      | natural y =>
        have evaluated : ((operation.eval x y).bind fun value =>
            some (Function.update values target (.natural value)))=some next := by
          simpa [RuntimeCommand.eval,hx,hy,Cell.nat?] using heval
        obtain ⟨value,hoperation,equal⟩:=Option.bind_eq_some_iff.mp evaluated
        have same : Function.update values target (.natural value)=next := Option.some.inj equal
        subst next
        obtain ⟨trace,hh,hl,hchain,ht,afterHeader,afterFrame,memory⟩ :=
          natBinarySlots_trace_memory program input before base left right target x y value n k operation values
            header valid.1 valid.2.1 valid.2.2 hx hy hbase hoperation fetch
        refine ⟨trace,natBinarySlotsResult before base left right target x y value,hh,hl,hchain,ht.trans (by decide),
          afterHeader,?_,rfl,afterFrame,rfl,memory⟩
        exact hbase

def runtimeCode (commands : List RuntimeCommand) : List Instruction := commands.flatMap RuntimeCommand.code

def runtimeEval : List RuntimeCommand → (ℕ → Cell) → Option (ℕ → Cell)
  | [],values => some values
  | command::commands,values => (command.eval values).bind (runtimeEval commands)

theorem runtimeCode_length_le (commands : List RuntimeCommand) : (runtimeCode commands).length ≤ 10*commands.length := by
  induction commands with
  | nil => simp [runtimeCode]
  | cons command commands ih =>
    have bound:=command.code_length_le
    change (command.code++runtimeCode commands).length ≤ 10*(command::commands).length
    simp only [List.length_append,List.length_cons]
    omega

/-- Every actual state of the literal mixed scalar block has the same
exact Header48 footprint. This finite compiler lemma consumes only true
local scalar evaluations, not an assumed whole-algorithm execution. -/
theorem runtimeCode_trace_memory (commands : List RuntimeCommand) (program : Program) (input : List Cell)
    (before : State) (base n k : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands,command.Valid) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (heval : runtimeEval commands values=some next)
    (fetch : FetchesCode program before.pc (runtimeCode commands)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 330*(commands.length+1) ∧ Header after base next ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(runtimeCode commands).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  induction commands generalizing before values with
  | nil =>
    have same : values=next := Option.some.inj heval
    subst next
    refine ⟨[before],before,rfl,rfl,.singleton before,(time_singleton_le program before).trans (by decide),header,hbase,rfl,
      ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,?_⟩
    intro state member
    have same : state=before := by simpa only [List.mem_singleton] using member
    subst state
    exact HeaderMemory.refl before base
  | cons command commands ih =>
    obtain ⟨middleValues,firstEval,tailEval⟩:=Option.bind_eq_some_iff.mp heval
    have firstFetch : FetchesCode program before.pc command.code := fetch.append_left
    obtain ⟨firstTrace,middle,firstHead,firstLast,firstChain,firstTime,middleHeader,middleBase,middlePC,firstFrame,firstOutput,firstMemory⟩ :=
      command.trace_memory program input before base n k values middleValues (valid command (by simp)) header hbase firstEval firstFetch
    have tailFetch : FetchesCode program middle.pc (runtimeCode commands) := by
      rw [middlePC]
      exact fetch.append_right
    have tailValid : ∀ item ∈ commands,item.Valid := fun item member => valid item (by simp only [List.mem_cons]; exact Or.inr member)
    obtain ⟨tail,after,tailHead,tailLast,tailChain,tailTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,tailMemory⟩ :=
      ih middle middleValues tailValid middleHeader middleBase tailEval tailFetch
    have joined:=joinTrace_spec program input firstTrace tail before middle after 330 (330*(commands.length+1))
      firstHead firstLast tailHead tailLast firstChain tailChain firstTime tailTime
    refine ⟨joinTrace firstTrace tail,after,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,afterBase,?_,
      firstFrame.trans afterFrame,afterOutput.trans firstOutput,
      joinTrace_memory firstTrace tail before middle base firstLast firstMemory tailMemory⟩
    · calc
        _ ≤ 330+330*(commands.length+1) := joined.2.2.2
        _ = _ := by simp only [List.length_cons]; ring
    · rw [afterPC,middlePC]
      change before.pc+command.code.length+(runtimeCode commands).length=before.pc+(command.code++runtimeCode commands).length
      rw [List.length_append]
      omega

end PDCompute.Solver
