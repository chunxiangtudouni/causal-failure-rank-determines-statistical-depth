module

public import Paid.PDROC_D27Prepare_Prefix_001
public import Paid.PDROC_D27Prepare_Program_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Prefix

theorem code_getD_safe (code : List Instruction)
    (safe : ∀ instruction ∈ code, StraightInstruction instruction ∨ instruction = .halt) (offset : ℕ) :
    StraightInstruction ((code[offset]?).getD .halt) ∨ (code[offset]?).getD .halt = .halt := by
  cases chosen : code[offset]? with
  | none => exact Or.inr rfl
  | some instruction =>
      obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp chosen
      have member : instruction ∈ code := by rw [← value]; exact List.getElem_mem inside
      exact safe instruction member

theorem step_instruction (program : Program) (input : List Cell) (before after : State)
    (actual : step program input before = some after) :
    ∃ instruction : Instruction, program[before.pc]? = some instruction ∧
      instruction.execute input before = some after := Option.bind_eq_some_iff.mp actual

theorem terminal_fetch_straight_or_halt (address : ℕ) (instruction : Instruction)
    (above : pc 45 ≤ address) (fetched : Program.program[address]? = some instruction) :
    StraightInstruction instruction ∨ instruction = .halt := by
  obtain ⟨inside, _⟩ := Array.getElem?_eq_some_iff.mp fetched
  have lower : 11520 ≤ address := above
  have upper : address < 11776 := by simpa only [program_size] using inside
  let offset := address - pc 45
  have offsetSmall : offset < pageWidth := by change address - 11520 < 256; omega
  have normalize : pc 45 + offset = address := by dsimp only [offset]; omega
  have pageFetch := program_fetch 45 offset (by decide) offsetSmall
  rw [normalize] at pageFetch
  have same := Option.some.inj (fetched.symm.trans pageFetch)
  have safe : ∀ instruction ∈ pageCode 45, StraightInstruction instruction ∨ instruction = .halt := by
    intro instruction member
    have layout : pageCode 45 = emitPrepared ++ [.halt] := rfl
    rw [layout] at member
    rcases List.mem_append.mp member with body | terminal
    · left
      have straight : StraightCode emitPrepared := outputSequence_straight (List.range 13)
      exact straight instruction body
    · exact Or.inr (List.mem_singleton.mp terminal)
  have selected := code_getD_safe (pageCode 45) safe offset
  exact same.symm ▸ selected

theorem terminal_step_forward (input : List Cell) (before after : State)
    (actual : step Program.program input before = some after) (above : pc 45 ≤ before.pc) :
    before.pc < after.pc := by
  obtain ⟨instruction, fetched, executed⟩ := step_instruction Program.program input before after actual
  rcases terminal_fetch_straight_or_halt before.pc instruction above fetched with straight | halted
  · have advanced := execute_pc_succ instruction straight input before after executed
    omega
  · subst instruction
    simp only [Instruction.execute] at executed
    cases executed

/-- Every actually executed state before the pc45 cut fetches strictly
below it. A core embedding may therefore replace that continuation. -/
theorem preFinal_trace_pc (input : List Cell) (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step Program.program input a = some b))
    (last : trace.getLast? = some final) (atCut : final.pc = pc 45) :
    ∀ state ∈ trace.dropLast, state.pc < pc 45 :=
  (chain_pc_cut Program.program input (pc 45) (terminal_step_forward input) trace final chain last atCut).2

/-- Cost equality is on the executed prefix dropLast. The newly fetched
pc45 continuation is charged by the actual core code, not silently reused. -/
theorem preFinal_executed_time_eq (newProgram : Program) (input : List Cell)
    (same : ∀ address < pc 45, Program.program[address]? = newProgram[address]?)
    (trace : List State) (final : State)
    (chain : trace.IsChain (fun a b => step Program.program input a = some b))
    (last : trace.getLast? = some final) (atCut : final.pc = pc 45) :
    time Program.program trace.dropLast = time newProgram trace.dropLast := by
  exact congrArg List.length (primitiveTrace_eq_of_code_agreement Program.program newProgram (pc 45) same
    trace.dropLast (preFinal_trace_pc input trace final chain last atCut))

end PDROC.D27Prepare.Prefix
