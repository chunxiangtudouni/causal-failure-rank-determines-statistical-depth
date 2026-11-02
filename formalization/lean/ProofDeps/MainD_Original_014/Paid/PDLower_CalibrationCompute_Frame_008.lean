module

public import Paid.PDLower_CalibrationCompute_CodeFacts_005
public import Paid.PDMenu_ComputeFrame_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def noInput : Instruction → Bool
  | .loadInput _ _ => false
  | _ => true

theorem noInput_correct (instruction : Instruction) :
    noInput instruction = true ↔ PDMenu.ComputeFrame.NoInputInstruction instruction := by
  cases instruction <;> simp [noInput,PDMenu.ComputeFrame.NoInputInstruction]

set_option maxRecDepth 4096 in
theorem basicBlock_noInput (label : Label) : (basicBlock label).body.all noInput = true := by
  cases label <;> rfl

theorem controlInstruction_noInput (origin : ℕ) (control : Control) :
    noInput (controlInstruction origin control) = true := by
  cases control <;> rfl

theorem compiledBlock_noInput (origin : ℕ) (label : Label) :
    ∀ instruction ∈ compiledBlock origin label,PDMenu.ComputeFrame.NoInputInstruction instruction := by
  intro instruction member
  rcases List.mem_append.mp member with body | control
  · exact (noInput_correct instruction).mp ((List.all_eq_true.mp (basicBlock_noInput label)) instruction body)
  · have eq : instruction = controlInstruction origin (basicBlock label).control := List.mem_singleton.mp control
    rw [eq]
    exact (noInput_correct _).mp (controlInstruction_noInput origin (basicBlock label).control)

theorem kernel_noInput (origin : ℕ) (offset : ℕ) (_bound : offset < (kernel origin).size)
    (instruction : Instruction) (fetched : (kernel origin)[offset]? = some instruction) :
    PDMenu.ComputeFrame.NoInputInstruction instruction := by
  have occurrence : (labels.flatMap (compiledBlock origin))[offset]? = some instruction := by
    simpa only [kernel,List.getElem?_toArray] using fetched
  have member : instruction ∈ labels.flatMap (compiledBlock origin) := List.mem_of_getElem? occurrence
  obtain ⟨label,_labelMember,instructionMember⟩ := List.mem_flatMap.mp member
  exact compiledBlock_noInput origin label instruction instructionMember

/-- The original literal calibration kernel can execute unchanged in the
real core's code and readonly input. Its concrete IsChain and loop/range
invariants remain separate actual-program obligations, not oracles. -/
theorem kernel_chain_in_caller (beforeCode suffix : Program) (leftInput rightInput : List Cell)
    (trace : List State)
    (scope : ∀ state ∈ trace.dropLast,beforeCode.size ≤ state.pc ∧ state.pc < beforeCode.size+(kernel beforeCode.size).size)
    (chain : trace.IsChain (fun before after =>
      step (PDMenu.ComputeFrame.locatedBlock beforeCode.size (kernel beforeCode.size)) leftInput before = some after)) :
    trace.IsChain (fun before after => step (beforeCode++kernel beforeCode.size++suffix) rightInput before = some after) ∧
      time (beforeCode++kernel beforeCode.size++suffix) trace ≤
        time (PDMenu.ComputeFrame.locatedBlock beforeCode.size (kernel beforeCode.size)) trace+15 :=
  PDMenu.ComputeFrame.chain_appendBlock beforeCode (kernel beforeCode.size) suffix leftInput rightInput trace scope
    (kernel_noInput beforeCode.size) chain

theorem kernel_chain_physical_caller (beforeCode suffix : Program) (leftInput rightInput : List Cell)
    (trace : List State)
    (scope : ∀ state ∈ trace.dropLast,beforeCode.size ≤ state.pc ∧ state.pc < beforeCode.size+(kernel beforeCode.size).size)
    (chain : trace.IsChain (fun before after =>
      step (PDMenu.ComputeFrame.locatedBlock beforeCode.size (kernel beforeCode.size)) leftInput before = some after)) :
    (trace.map codeState).IsChain (fun before after =>
      codeStep (encodeProgram (beforeCode++kernel beforeCode.size++suffix)) rightInput before = some after) ∧
      (codePrimitiveTrace (encodeProgram (beforeCode++kernel beforeCode.size++suffix)) (trace.map codeState)).length ≤
        time (PDMenu.ComputeFrame.locatedBlock beforeCode.size (kernel beforeCode.size)) trace+15 :=
  PDMenu.ComputeFrame.chain_appendBlock_physicalCode beforeCode (kernel beforeCode.size) suffix leftInput rightInput trace scope
    (kernel_noInput beforeCode.size) chain

end PDLower.CalibrationCompute
