module

public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute

open PaperProofs.Paid.Computation

theorem registerFromWord_word (register : Register) : registerFromWord (registerWord register) = some register := by
  exact PaperProofs.Structure.LaminarTree.IndexedRAM.Register.fromWord_word register

theorem natOpFromWord_word (operation : NatOp) : NatOp.fromWord operation.word = some operation := by
  cases operation <;> rfl

theorem ratOpFromWord_word (operation : RatOp) : RatOp.fromWord operation.word = some operation := by
  cases operation <;> rfl

theorem comparisonFromWord_word (comparison : Comparison) : Comparison.fromWord comparison.word = some comparison := by
  cases comparison <;> rfl

theorem instructionDecode_encode (instruction : Instruction) :
    Instruction.decodeWords instruction.encodeWords = some instruction := by
  cases instruction <;> simp [Instruction.encodeWords, Instruction.decodeWords, Cell.nat?,
    registerFromWord_word, natOpFromWord_word, ratOpFromWord_word, comparisonFromWord_word]

theorem encodeProgram_length (program : Program) : (encodeProgram program).length = 5 * program.size := by
  simp only [encodeProgram, List.length_flatMap, Vector.length_toList, List.map_const',
    List.sum_replicate, Array.length_toList, Nat.nsmul_eq_mul]
  omega

theorem fetchInstruction_append (pre code : List Cell) (pc : ℕ) :
    fetchInstruction (pre ++ code) (pre.length + pc) = fetchInstruction code pc := by
  have hread (index : ℕ) : (pre ++ code)[pre.length + index]? = code[index]? := by
    rw [List.getElem?_append_right (by omega : pre.length ≤ pre.length + index)]
    simp only [Nat.add_sub_cancel_left]
  simp only [fetchInstruction, Nat.add_assoc, hread]

theorem fetchInstruction_head (instruction : Instruction) (tail : List Cell) :
    fetchInstruction (instruction.encodeWords.toList ++ tail) 0 = some instruction := by
  have hread (position : Fin 5) :
      (instruction.encodeWords.toList ++ tail)[position.val]? = some instruction.encodeWords[position] := by
    rw [List.getElem?_append_left (by simp)]
    simp
  simp only [fetchInstruction, Nat.zero_add, hread ⟨0, by omega⟩, hread ⟨1, by omega⟩,
    hread ⟨2, by omega⟩, hread ⟨3, by omega⟩, hread ⟨4, by omega⟩, Option.bind_eq_bind, Option.bind_some]
  convert instructionDecode_encode instruction using 1
  congr 1
  apply Vector.ext
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases h with h | h | h | h | h <;> subst i <;> rfl

theorem fetchInstruction_list (program : List Instruction) (pc : ℕ) :
    fetchInstruction (program.flatMap (fun instruction => instruction.encodeWords.toList)) (5 * pc) = program[pc]? := by
  induction program generalizing pc with
  | nil => simp [fetchInstruction]
  | cons instruction later ih =>
    cases pc with
    | zero => simpa only [List.flatMap_cons, Nat.mul_zero, List.getElem?_cons_zero] using fetchInstruction_head instruction _
    | succ pc =>
      rw [List.flatMap_cons, show 5 * (pc + 1) = instruction.encodeWords.toList.length + 5 * pc by simp; omega,
        fetchInstruction_append, ih, List.getElem?_cons_succ]

theorem fetchInstruction_encode (program : Program) (pc : ℕ) :
    fetchInstruction (encodeProgram program) (5 * pc) = program[pc]? := by
  simpa only [encodeProgram, Array.getElem?_toList] using fetchInstruction_list program.toList pc

theorem instructionExecuteCode_simulation (instruction : Instruction) (input : List Cell) (state : State) :
    instruction.executeCode input (codeState state) = (instruction.execute input state).map codeState := by
  cases instruction <;> simp [Instruction.executeCode, Instruction.execute, State.set, codeState,
    Option.map_bind, Option.bind_assoc, Function.comp_def, Nat.mul_add]
  congr 1
  funext address
  split_ifs <;> simp_all

theorem codeStep_simulation (program : Program) (input : List Cell) (state : State) :
    codeStep (encodeProgram program) input (codeState state) = (step program input state).map codeState := by
  simp only [codeStep, codeState, fetchInstruction_encode, step]
  cases h : program[state.pc]? with
  | none => rfl
  | some instruction => exact instructionExecuteCode_simulation instruction input state

theorem codeState_initial : codeState initial = initial := rfl

theorem codeRuns_of_runs (program : Program) (input : List Cell) (trace : List State) (final : State)
    (h : Runs program input trace final) :
    CodeRuns (encodeProgram program) input (trace.map codeState) (codeState final) := by
  rcases h with ⟨hhead, hchain, hlast, hhalt, heval⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.head?_map, hhead, Option.map_some, codeState_initial]
  · apply List.isChain_map_of_isChain codeState ?_ hchain
    intro before after hstep
    rw [codeStep_simulation, hstep]
    rfl
  · simp only [List.getLast?_map, hlast, Option.map_some]
  · simpa only [codeState, fetchInstruction_encode] using hhalt
  · obtain ⟨hreach, hterminal⟩ := StateTransition.mem_eval.mp heval
    apply StateTransition.mem_eval.mpr
    constructor
    · have h := Relation.ReflTransGen.lift codeState (p := fun before after =>
          after ∈ codeStep (encodeProgram program) input before)
        (fun before after hs => by
          change step program input before = some after at hs
          change codeStep (encodeProgram program) input (codeState before) = some (codeState after)
          rw [codeStep_simulation, hs]
          rfl) initial final hreach
      change StateTransition.Reaches (codeStep (encodeProgram program) input) (codeState initial) (codeState final) at h
      simpa only [codeState_initial] using h
    · rw [codeStep_simulation, hterminal]
      rfl

theorem codePrimitiveTrace_eq (program : Program) (trace : List State) :
    codePrimitiveTrace (encodeProgram program) (trace.map codeState) = primitiveTrace program trace := by
  simp only [codePrimitiveTrace, primitiveTrace, List.flatMap_map,
    codeState, fetchInstruction_encode]

theorem codeRefinementClaims : CodeRefinementClaims :=
  ⟨instructionDecode_encode, fetchInstruction_encode, codeStep_simulation, codeRuns_of_runs,
    codePrimitiveTrace_eq, encodeProgram_length⟩

end PDCompute


