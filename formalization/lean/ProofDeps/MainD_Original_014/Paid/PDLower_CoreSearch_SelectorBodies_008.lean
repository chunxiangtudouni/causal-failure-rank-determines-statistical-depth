module

public import Paid.PDLower_CoreSearch_TargetMemory_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch

def selectorConstantsCommands : List HeaderCommand := [.constant 41 (.rational 0),.constant 42 (.rational 1)]
def selectorZeroCommands : List HeaderCommand := [.constant 29 (.rational 0)]
def selectorOneCommands : List HeaderCommand := [.constant 29 (.rational 1)]
def selectorCopyCommands : List HeaderCommand := [.copy 31 29]

theorem selectorConstants_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (headerCode selectorConstantsCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤135 ∧
      Header after 0 (Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+8 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have valid : ∀ command∈selectorConstantsCommands,command.Valid := by
    intro command member
    simp only [selectorConstantsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide
  have targets : ∀ command∈selectorConstantsCommands,commandTarget command∈scalarRegion := by
    intro command member
    simp only [selectorConstantsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst command <;> decide
  have evaluated : headerEval selectorConstantsCommands values=
      some (Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)) := rfl
  have length : (headerCode selectorConstantsCommands).length=8 := rfl
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar selectorConstantsCommands program input before values _ valid targets header fresh evaluated fetched
  exact ⟨trace,after,head,last,chain,by simpa only [length] using cost,afterHeader,afterFresh,
    by simpa only [length] using pc,output,memory⟩

theorem selectorZero_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (headerCode selectorZeroCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 29 (.rational 0)) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have valid : ∀ command∈selectorZeroCommands,command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    dsimp only [HeaderCommand.Valid,headerWords]
    decide
  have targets : ∀ command∈selectorZeroCommands,commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    decide
  have length : (headerCode selectorZeroCommands).length=4 := rfl
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar selectorZeroCommands program input before values _ valid targets header fresh rfl fetched
  exact ⟨trace,after,head,last,chain,by simpa only [length] using cost,afterHeader,afterFresh,
    by simpa only [length] using pc,output,memory⟩

theorem selectorOne_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (fetched : FetchesCode program before.pc (headerCode selectorOneCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤75 ∧
      Header after 0 (Function.update values 29 (.rational 1)) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+4 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have valid : ∀ command∈selectorOneCommands,command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    dsimp only [HeaderCommand.Valid,headerWords]
    decide
  have targets : ∀ command∈selectorOneCommands,commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    decide
  have length : (headerCode selectorOneCommands).length=4 := rfl
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar selectorOneCommands program input before values _ valid targets header fresh rfl fetched
  exact ⟨trace,after,head,last,chain,by simpa only [length] using cost,afterHeader,afterFresh,
    by simpa only [length] using pc,output,memory⟩

theorem selectorCopy_trace (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (weight : ℚ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (ratio : values 31=.rational weight)
    (fetched : FetchesCode program before.pc (headerCode selectorCopyCommands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace≤105 ∧
      Header after 0 (Function.update values 29 (.rational weight)) ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+6 ∧ after.output=before.output ∧
      ∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0 := by
  have valid : ∀ command∈selectorCopyCommands,command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    dsimp only [HeaderCommand.Valid,headerWords]
    decide
  have targets : ∀ command∈selectorCopyCommands,commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    decide
  have evaluated : headerEval selectorCopyCommands values=some (Function.update values 29 (.rational weight)) := by
    simp [selectorCopyCommands,headerEval,HeaderCommand.eval,ratio]
  have length : (headerCode selectorCopyCommands).length=6 := rfl
  obtain ⟨trace,after,head,last,chain,cost,_run,afterHeader,afterFresh,pc,output,memory⟩ :=
    commands_trace_scalar selectorCopyCommands program input before values _ valid targets header fresh evaluated fetched
  exact ⟨trace,after,head,last,chain,by simpa only [length] using cost,afterHeader,afterFresh,
    by simpa only [length] using pc,output,memory⟩

end PDLower.CoreSearch
