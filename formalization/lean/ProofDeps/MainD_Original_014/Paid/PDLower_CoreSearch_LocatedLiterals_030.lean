module

public import Paid.PDLower_CoreSearch_LocatedSegment_029
public import Paid.PDLower_CoreSearch_SelectorBodies_008
public import Paid.PDCompute_SolverCopyConstantBits_163

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

namespace PDLower.CoreSearch.Located

theorem copyConstant_segment_bits (commands : List HeaderCommand) (program : Program) (input : List Cell) (before : State)
    (values next : ℕ→Cell) (budget : ℕ) (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next) (safe : RootD27.Bits.SafeBits before budget)
    (bounded : ∀ command∈commands,CopyConstantBound budget command) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+(headerCode commands).length)≤budget)
    (fetched : FetchesCode program before.pc (headerCode commands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+(headerCode commands).length≤high) :
    ∃ after : State,LocatedSegment program input before after (15*((headerCode commands).length+1)) budget low high ∧
      Header after 0 next ∧ after.register .fresh=.natural 0 ∧ after.pc=before.pc+(headerCode commands).length := by
  obtain ⟨after,actual,afterHeader,afterFresh,pc,_run⟩ := LocatedSegment.commands commands program input before values next budget
    valid targets header fresh evaluated safe
    (copyConstantCommands_evaluated_bits commands values budget valid (HeaderValueBits.of_safe header safe) bounded) addressBits pcBits fetched low high pcLower pcUpper
  exact ⟨after,actual,afterHeader,afterFresh,pc⟩

theorem literal_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (target budget : ℕ) (value : Cell) (inside : target∈scalarRegion) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (safe : RootD27.Bits.SafeBits before budget)
    (valueBits : value.bits≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+4)≤budget)
    (fetched : FetchesCode program before.pc (headerCode [.constant target value]))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+4≤high) :
    ∃ after : State,LocatedSegment program input before after 75 budget low high ∧ Header after 0 (Function.update values target value) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+4 := by
  have targetInside : target<headerWords := by
    simp only [scalarRegion,Finset.mem_Icc] at inside
    unfold headerWords
    omega
  have valid : ∀ command∈[HeaderCommand.constant target value],command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact targetInside
  have targets : ∀ command∈[HeaderCommand.constant target value],commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact inside
  have bounded : ∀ command∈[HeaderCommand.constant target value],CopyConstantBound budget command := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact valueBits
  have length : (headerCode [.constant target value]).length=4 := rfl
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := copyConstant_segment_bits [.constant target value] program input before values
    (Function.update values target value) budget valid targets header fresh rfl safe bounded addressBits
    (by simpa only [length] using pcBits) fetched low high pcLower (by simpa only [length] using pcUpper)
  exact ⟨after,by simpa only [length] using actual,afterHeader,afterFresh,by simpa only [length] using pc⟩

theorem copy_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell)
    (source target budget : ℕ) (sourceInside : source<headerWords) (inside : target∈scalarRegion) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0) (safe : RootD27.Bits.SafeBits before budget)
    (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+6)≤budget)
    (fetched : FetchesCode program before.pc (headerCode [.copy source target]))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+6≤high) :
    ∃ after : State,LocatedSegment program input before after 105 budget low high ∧ Header after 0 (Function.update values target (values source)) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+6 := by
  have targetInside : target<headerWords := by
    simp only [scalarRegion,Finset.mem_Icc] at inside
    unfold headerWords
    omega
  have valid : ∀ command∈[HeaderCommand.copy source target],command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact ⟨sourceInside,targetInside⟩
  have targets : ∀ command∈[HeaderCommand.copy source target],commandTarget command∈scalarRegion := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact inside
  have bounded : ∀ command∈[HeaderCommand.copy source target],CopyConstantBound budget command := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    trivial
  have length : (headerCode [.copy source target]).length=6 := rfl
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := copyConstant_segment_bits [.copy source target] program input before values
    (Function.update values target (values source)) budget valid targets header fresh rfl safe bounded addressBits
    (by simpa only [length] using pcBits) fetched low high pcLower (by simpa only [length] using pcUpper)
  exact ⟨after,by simpa only [length] using actual,afterHeader,afterFresh,by simpa only [length] using pc⟩

theorem selectorConstants_segment_bits (program : Program) (input : List Cell) (before : State) (values : ℕ→Cell) (budget : ℕ)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits headerWords≤budget) (pcBits : natBits (before.pc+8)≤budget)
    (fetched : FetchesCode program before.pc (headerCode selectorConstantsCommands))
    (low high : ℕ) (pcLower : low≤before.pc) (pcUpper : before.pc+8≤high) :
    ∃ after : State,LocatedSegment program input before after 135 budget low high ∧
      Header after 0 (Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)) ∧
      after.register .fresh=.natural 0 ∧ after.pc=before.pc+8 := by
  have valid : ∀ command∈selectorConstantsCommands,command.Valid := by
    intro command member
    simp only [selectorConstantsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst command <;> dsimp only [HeaderCommand.Valid,headerWords] <;> decide
  have targets : ∀ command∈selectorConstantsCommands,commandTarget command∈scalarRegion := by
    intro command member
    simp only [selectorConstantsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst command <;> decide
  have bounded : ∀ command∈selectorConstantsCommands,CopyConstantBound budget command := by
    intro command member
    simp only [selectorConstantsCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same <;> subst command <;>
      change 1+ratEncodingBits _≤budget <;> norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits] <;> omega
  have length : (headerCode selectorConstantsCommands).length=8 := rfl
  obtain ⟨after,actual,afterHeader,afterFresh,pc⟩ := copyConstant_segment_bits selectorConstantsCommands program input before values
    (Function.update (Function.update values 41 (.rational 0)) 42 (.rational 1)) budget valid targets header fresh rfl safe bounded addressBits
    (by simpa only [length] using pcBits) fetched low high pcLower (by simpa only [length] using pcUpper)
  exact ⟨after,by simpa only [length] using actual,afterHeader,afterFresh,by simpa only [length] using pc⟩

end PDLower.CoreSearch.Located
