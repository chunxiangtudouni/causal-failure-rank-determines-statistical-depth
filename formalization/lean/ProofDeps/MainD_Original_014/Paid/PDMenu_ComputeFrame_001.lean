module

public import PaperProofs.Paid.PDCompute_CodeRefinement_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

def NoInputInstruction : Instruction → Prop
  | .loadInput _ _ => False
  | _ => True

theorem execute_eq_of_noInput (instruction : Instruction) (h : NoInputInstruction instruction)
    (left right : List Cell) (state : State) :
    instruction.execute left state = instruction.execute right state := by
  cases instruction <;> first | rfl | exact False.elim h

theorem step_eq_of_fetch_eq (left right : Program) (input : List Cell) (state : State)
    (h : left[state.pc]? = right[state.pc]?) : step left input state = step right input state := by
  simp only [step, h]

theorem step_eq_of_fetch_eq_noInput (left right : Program) (leftInput rightInput : List Cell)
    (state : State) (h : left[state.pc]? = right[state.pc]?)
    (hno : ∀ instruction, left[state.pc]? = some instruction → NoInputInstruction instruction) :
    step left leftInput state = step right rightInput state := by
  cases hf : left[state.pc]? with
  | none => simp [step, hf, ← h]
  | some instruction =>
      have hr := h.symm.trans hf
      simp only [step, hf, hr]
      exact execute_eq_of_noInput instruction (hno instruction hf) leftInput rightInput state

/-- Direct labels are already generated with their final absolute origin.
Only the fetched array segment is framed; indirect return values are kept. -/
def locatedBlock (origin : ℕ) (code : Program) : Program := Array.replicate origin .halt ++ code

theorem locatedBlock_fetch (origin : ℕ) (code : Program) (offset : ℕ) :
    (locatedBlock origin code)[origin+offset]? = code[offset]? := by
  unfold locatedBlock
  rw [Array.getElem?_append_right (by simp only [Array.size_replicate]; omega)]
  simp only [Array.size_replicate, Nat.add_sub_cancel_left]

theorem appendBlock_fetch (beforeCode code suffix : Program) (offset : ℕ) (hoff : offset < code.size) :
    (beforeCode ++ code ++ suffix)[beforeCode.size+offset]? = code[offset]? := by
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega),
    Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem appendBlock_fetch_located (beforeCode code suffix : Program) (state : State)
    (hlo : beforeCode.size ≤ state.pc) (hhi : state.pc < beforeCode.size+code.size) :
    (locatedBlock beforeCode.size code)[state.pc]? = (beforeCode ++ code ++ suffix)[state.pc]? := by
  have hp : state.pc = beforeCode.size+(state.pc-beforeCode.size) := by omega
  rw [hp, locatedBlock_fetch, appendBlock_fetch beforeCode code suffix _ (by omega)]

theorem step_jumpIndirect_return (program : Program) (input : List Cell) (state : State) (address : ℕ)
    (hf : program[state.pc]? = some (.jumpIndirect .old))
    (hr : state.register .old = .natural address) :
    step program input state = some {state with pc := address} := by
  simp [step, hf, Instruction.execute, hr, Cell.nat?]

theorem instruction_primitives_length_le (instruction : Instruction) : instruction.primitives.length ≤ 15 := by
  cases instruction <;> simp [Instruction.primitives, Instruction.operations]

theorem fetched_primitives_length_le (program : Program) (state : State) :
    (((program[state.pc]?).map Instruction.primitives).getD []).length ≤ 15 := by
  cases hf : program[state.pc]? with
  | none => simp only [Option.map_none, Option.getD_none, List.length_nil]; omega
  | some instruction =>
      simpa only [hf, Option.map_some, Option.getD_some] using instruction_primitives_length_le instruction

theorem time_append (program : Program) (left right : List State) :
    time program (left++right) = time program left+time program right := by
  simp only [time, primitiveTrace, List.flatMap_append, List.length_append]

theorem time_singleton_le (program : Program) (state : State) : time program [state] ≤ 15 := by
  simpa only [time, primitiveTrace, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    fetched_primitives_length_le program state

end PDMenu.ComputeFrame
