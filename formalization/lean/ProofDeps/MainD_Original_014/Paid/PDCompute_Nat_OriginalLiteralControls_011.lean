module
public import Paid.PDCompute_Nat_ControlContext_010
public import Paid.PDCompute_Pack_CopyBits_085
public import Paid.PDCompute_SolverSequenceBits_155
public import Paid.PDCompute_SolverTerminalFields_095

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

/-- Actual four-op constant control; target19/20 initializes counters,
and target46 selects the original row0/tool0 guard. Old cells keep B. -/
theorem constantControl_trace_bits (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k budget target value : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (inside : target<headerWords)
    (bounded : value≤PDCompute.Pack.naturalCap base n k)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc (headerCode [.constant target (.natural value)])) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤330 ∧ Header after base (Function.update values target (.natural value)) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(headerCode [.constant target (.natural value)]).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have evaluated : HeaderEvaluatedBits budget [.constant target (.natural value)] values:=
    ⟨_,rfl,(HeaderValueBits.of_safe header safe).update (context.natural value bounded),True.intro⟩
  exact headerCode_trace_bits [.constant target (.natural value)] _ input before base n k budget values _
    (by intro command member;have same:=List.mem_singleton.mp member;subst command;exact inside) header fresh rfl safe evaluated context.header
    (SolverControlContext.block (before:=before) context _ (by change (0:ℕ)<4;decide) fetch) fetch

/-- Original finish-row code really starts with copy35->37. It is never
replaced by the provisional rowPointerValues37 formula. -/
theorem finishRowFields_copy_fetch (program : Program) (counter : ℕ)
    (fetch : FetchesCode program counter (headerCode finishRowFieldsCommands)) : FetchesCode program counter (copySlot 35 37) := by
  change FetchesCode program counter (copySlot 35 37++headerCode (terminalFieldsCommands false)) at fetch
  exact fetch.append_left

theorem rowZeroWritePointer_trace_bits (mode : ReaderMode) (origin : ℕ) (input : List Cell) (caller before : State)
    (incoming base n k column budget : ℕ) (values : ℕ → Cell)
    (context : SolverControlContext caller incoming base n k mode origin budget)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (safe : RootD27.Bits.SafeBits before budget) (rowZero : values 19=.natural 0)
    (good : values 35=.natural (cellBase base k 0 column))
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc (headerCode finishRowFieldsCommands)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun a b=>step (solverLocatedProgram mode origin) input a=some b) ∧
      time (solverLocatedProgram mode origin) trace≤105 ∧ Header after base (Function.update values 37 (values 35)) ∧
      after.heap (base+37)=.natural (cellBase base k 0 column) ∧ after.heap (base+19)=.natural 0 ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+6 ∧ Frame before after base n k ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base ∧ RootD27.Bits.SafeBits state budget := by
  have actualFetch:=finishRowFields_copy_fetch _ before.pc fetch
  obtain ⟨trace,head,last,chain,cost,afterHeader,afterFresh,afterPC,output,memory,bits⟩:=PDCompute.Pack.copy_trace_safe _ input before base 35 37 budget values header
    (by decide) (by decide) fresh safe
    (context.natural _ (PDCompute.Pack.naturalCap_header_address base n k 35 (by decide)))
    (context.natural _ (PDCompute.Pack.naturalCap_header_address base n k 37 (by decide)))
    (SolverControlContext.block (before:=before) context _ (by decide) actualFetch) actualFetch
  let after:=copySlotResult before base 35 37
  have finalMemory:=HeaderMemory.trace_last memory last
  refine ⟨trace,after,head,last,chain,cost,afterHeader,?_,?_,afterFresh,afterPC,finalMemory.frame n k,output,
    fun state member=>⟨memory state member,bits state member⟩⟩
  · exact (afterHeader.value 37 (by decide)).trans (by simpa only [Function.update_self] using good)
  · exact (afterHeader.value 19 (by decide)).trans (by simpa only [Function.update_of_ne (by decide : (19:ℕ)≠37)] using rowZero)

end PDCompute.NatControl
