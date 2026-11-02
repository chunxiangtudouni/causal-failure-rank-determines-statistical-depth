module

public import Paid.PDCompute_SolverCopyConstantBits_163
public import Paid.PDCompute_SolverTerminalFields_095
public import Paid.PDCompute_SolverZeroBadRuntime_083

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

theorem acceptRepairCommands_copyBound (budget : ℕ) (small : 4≤budget) :
    ∀ command∈acceptRepairCommands,CopyConstantBound budget command := by
  intro command member
  simp only [acceptRepairCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst command <;>
    norm_num [CopyConstantBound,Cell.bits,natBits,ratEncodingBits,ratNumBits,ratDenBits]
  all_goals omega

theorem minimumUpdateCommands_copyBound (budget : ℕ) :
    ∀ command∈minimumUpdateCommands,CopyConstantBound budget command := by
  intro command member
  simp only [minimumUpdateCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h <;> subst command <;> trivial

theorem zeroBadCommands_copyBound (budget : ℕ) (small : 4≤budget) :
    ∀ command∈zeroBadCommands,CopyConstantBound budget command := by
  intro command member
  simp only [zeroBadCommands,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h <;> subst command <;>
    norm_num [CopyConstantBound,Cell.bits,natBits,ratEncodingBits,ratNumBits,ratDenBits]
  all_goals omega

theorem terminalFieldsCommands_copyBound (abandon : Bool) (budget : ℕ) (small : 4≤budget) :
    ∀ command∈terminalFieldsCommands abandon,CopyConstantBound budget command := by
  cases abandon <;> intro command member <;>
    simp only [terminalFieldsCommands,List.mem_cons,List.not_mem_nil,or_false] at member <;>
    rcases member with h|h|h|h|h|h <;> subst command <;>
    norm_num [CopyConstantBound,Cell.bits,natBits,ratEncodingBits,ratNumBits,ratDenBits]
  all_goals omega

theorem finishRowFieldsCommands_copyBound (budget : ℕ) (small : 4≤budget) :
    ∀ command∈finishRowFieldsCommands,CopyConstantBound budget command := by
  intro command member
  rcases List.mem_cons.mp member with first|later
  · subst command
    trivial
  · exact terminalFieldsCommands_copyBound false budget small command later

theorem terminalFields_trace_bits (abandon : Bool) (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget)
    (pcBits : natBits (before.pc+(headerCode (terminalFieldsCommands abandon)).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode (terminalFieldsCommands abandon))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1155 ∧
      Header after base (terminalFieldsValues values abandon) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(headerCode (terminalFieldsCommands abandon)).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have cost : 165*((terminalFieldsCommands abandon).length+1)=1155 := rfl
  simpa only [cost] using copyConstant_trace_bits (terminalFieldsCommands abandon) program input before base n k budget values
    (terminalFieldsValues values abandon) (terminalFieldsCommands_valid abandon) header fresh (terminalFieldsCommands_eval abandon values)
    safe (terminalFieldsCommands_copyBound abandon budget small) addressBits pcBits fetch

theorem finishRowFields_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(headerCode finishRowFieldsCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode finishRowFieldsCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤1320 ∧
      Header after base (finishRowFieldsValues values) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(headerCode finishRowFieldsCommands).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have cost : 165*(finishRowFieldsCommands.length+1)=1320 := rfl
  simpa only [cost] using copyConstant_trace_bits finishRowFieldsCommands program input before base n k budget values
    (finishRowFieldsValues values) finishRowFieldsCommands_valid header fresh (finishRowFieldsCommands_eval values)
    safe (finishRowFieldsCommands_copyBound budget small) addressBits pcBits fetch

theorem zeroBad_trace_bits (program : Program) (input : List Cell) (before : State)
    (base n k budget : ℕ) (values : ℕ → Cell) (penalty : ℚ) (header : Header before base values)
    (fresh : before.register .fresh=.natural base) (hpenalty : values 2=.rational penalty)
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (addressBits : 1+natBits (base+headerWords)≤budget) (pcBits : natBits (before.pc+(headerCode zeroBadCommands).length)≤budget)
    (fetch : FetchesCode program before.pc (headerCode zeroBadCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤990 ∧
      Header after base (zeroBadValues values penalty) ∧ after.register .fresh=.natural base ∧
      after.pc=before.pc+(headerCode zeroBadCommands).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have cost : 165*(zeroBadCommands.length+1)=990 := rfl
  simpa only [cost] using copyConstant_trace_bits zeroBadCommands program input before base n k budget values
    (zeroBadValues values penalty) zeroBadCommands_valid header fresh (zeroBadCommands_eval values penalty hpenalty)
    safe (zeroBadCommands_copyBound budget small) addressBits pcBits fetch

end PDCompute.Solver
