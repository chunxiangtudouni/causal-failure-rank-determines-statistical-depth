module

public import Paid.PDMenu_ComputeFrame_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

/-- The same actual fragment executes after physical five-word encoding.
This is genuine adjacent codeStep transport, with no initial/HALT premise. -/
theorem chain_physicalCode (program : Program) (input : List Cell) (trace : List State)
    (hc : trace.IsChain (fun before after => step program input before = some after)) :
    (trace.map codeState).IsChain (fun before after => codeStep (encodeProgram program) input before = some after) := by
  apply List.isChain_map_of_isChain codeState ?_ hc
  intro before after hs
  rw [PDCompute.codeStep_simulation, hs]
  rfl

theorem physicalCode_time_eq (program : Program) (trace : List State) :
    (codePrimitiveTrace (encodeProgram program) (trace.map codeState)).length = time program trace :=
  congrArg List.length (PDCompute.codePrimitiveTrace_eq program trace)

/-- Full typed and physical-word phase transport for the heap-only callee.
The extra caller return-state fetch remains charged in the same bound. -/
theorem chain_appendBlock_physicalCode (beforeCode code suffix : Program) (leftInput rightInput : List Cell)
    (trace : List State)
    (hscope : ∀ state ∈ trace.dropLast, beforeCode.size ≤ state.pc ∧ state.pc < beforeCode.size+code.size)
    (hcode : ∀ offset, offset < code.size → ∀ instruction, code[offset]? = some instruction → NoInputInstruction instruction)
    (hc : trace.IsChain (fun before after => step (locatedBlock beforeCode.size code) leftInput before = some after)) :
    (trace.map codeState).IsChain (fun before after =>
      codeStep (encodeProgram (beforeCode++code++suffix)) rightInput before = some after) ∧
    (codePrimitiveTrace (encodeProgram (beforeCode++code++suffix)) (trace.map codeState)).length ≤
      time (locatedBlock beforeCode.size code) trace+15 := by
  have h := chain_appendBlock beforeCode code suffix leftInput rightInput trace hscope hcode hc
  exact ⟨chain_physicalCode _ _ _ h.1, (physicalCode_time_eq _ _).trans_le h.2⟩

end PDMenu.ComputeFrame
