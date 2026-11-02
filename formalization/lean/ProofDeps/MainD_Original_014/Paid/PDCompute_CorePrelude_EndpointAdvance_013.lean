module
public import Paid.PDCompute_CorePrelude_EntryCount_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section

namespace PDCompute.CorePrelude
open PaperProofs.Paid PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame RootD27.Endpoint

def RaisesEntry (origin : ℕ) (instruction : Instruction) : Prop :=
  ∀ (input : List Cell) (before after : State),origin≤before.pc →
    instruction.execute input before=some after → origin<after.pc

theorem straight_raises_entry (origin : ℕ) (instruction : Instruction)
    (straight : StraightInstruction instruction) : RaisesEntry origin instruction := by
  intro input before after lower actual
  have advanced:=execute_pc_succ instruction straight input before after actual
  omega

theorem jump_raises_entry (origin target : ℕ) (above : origin<target) :
    RaisesEntry origin (.jump target) := by
  intro input before after _ actual
  have same:=Option.some.inj actual
  subst after
  exact above

theorem branch_raises_entry (origin zeroPC nonzeroPC : ℕ) (register : Register)
    (low : origin<zeroPC) (high : origin<nonzeroPC) : RaisesEntry origin (.branchZero register zeroPC nonzeroPC) := by
  intro input before after _ actual
  cases value : before.register register with
  | natural count =>
    by_cases empty : count=0 <;>
      simp [Instruction.execute,value,Cell.nat?,empty] at actual <;> subst after
    · exact low
    · exact high
  | rational rationalValue => simp [Instruction.execute,value,Cell.nat?] at actual

/-- Every ORIGINAL105 initialization opcode either advances a straight
PC or targets the actual padding labels strictly above entry. There is
no indirect return in this literal initial fragment. -/
theorem initialization_raises_entry (origin : ℕ) :
    ∀ instruction∈initializationCode origin,RaisesEntry origin instruction := by
  intro instruction member
  simp only [initializationCode,List.mem_append] at member
  rcases member with (((prologue|padding)|loop)|scalar)|cache
  · exact straight_raises_entry origin instruction (prologue_straight instruction prologue)
  · apply straight_raises_entry origin instruction
    simp only [paddingSetup,List.mem_cons,List.not_mem_nil,or_false] at padding
    rcases padding with same|same|same <;> subst instruction <;> trivial
  · simp only [baseRowCode,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at loop
    rcases loop with (same|same)|body
    · subst instruction;exact straight_raises_entry _ _ (by trivial)
    · subst instruction;exact branch_raises_entry _ _ _ _ (by omega) (by omega)
    · simp only [baseRowBody,List.mem_cons,List.not_mem_nil,or_false] at body
      rcases body with same|same|same|same|same|same|same|same|same|same|same|same|same|same|same|same <;> subst instruction
      all_goals first | exact straight_raises_entry _ _ (by trivial) | exact jump_raises_entry _ _ (by omega)
  · exact straight_raises_entry origin instruction (headerCode_straight initialCommands instruction scalar)
  · exact straight_raises_entry origin instruction (cacheHeader_straight instruction cache)

theorem raising_trace_entry_count (program : Program) (input : List Cell) (origin : ℕ)
    (code : List Instruction) (before : State) (trace : List State)
    (head : trace.head?=some before) (position : before.pc=origin)
    (chain : trace.IsChain (fun first later=>step program input first=some later))
    (fetchedCode : FetchesCode program origin code)
    (scope : ∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+code.length)
    (raises : ∀ instruction∈code,RaisesEntry origin instruction) :
    PaperProofs.Paid.Computation.entryCount origin trace=1 := by
  apply entry_count_one origin trace before head position
  have greater:=chain_tail_property (fun first later=>step program input first=some later)
    (fun state=>origin<state.pc) trace chain (by
      intro first member later actual
      have bounds:=scope first member
      obtain ⟨instruction,fetched,executed⟩:=Option.bind_eq_some_iff.mp actual
      have addressed : origin+(first.pc-origin)=first.pc:=Nat.add_sub_of_le bounds.1
      have offset : first.pc-origin<code.length:=by omega
      have value : code[first.pc-origin]?=some instruction:=by
        rw [←fetchedCode (first.pc-origin) offset,addressed]
        exact fetched
      exact raises instruction (List.mem_of_getElem? value) input first later bounds.1 executed)
  intro state member equal
  have bound:=greater state member
  omega

attribute [local irreducible] initializationCode

theorem initialization_trace_entry_count (origin : ℕ) (input : List Cell) (before : State) (trace : List State)
    (head : trace.head?=some before) (position : before.pc=origin)
    (chain : trace.IsChain (fun first later=>
      step (locatedBlock origin (initializationCode origin).toArray) input first=some later)) :
    PaperProofs.Paid.Computation.entryCount origin trace=1 := by
  have scope:=PDLower.CalibrationCompute.located_chain_scope origin (initializationCode origin).toArray input trace chain
  exact raising_trace_entry_count _ input origin (initializationCode origin) before trace head position chain
    (by intro offset inside;rw [locatedBlock_fetch,List.getElem?_toArray])
    (by simpa only [List.size_toArray] using scope) (initialization_raises_entry origin)

end PDCompute.CorePrelude
