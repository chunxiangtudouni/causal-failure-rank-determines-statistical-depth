module

public import Structure.PSTR_BuildLower_ValueOps_003

/-! Real dimension-bank initialization and inline dynamic constants. All
physical addresses are parameters for the shared A06 prepare allocation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035b

variable {bits : Nat}

/-- Unlike the earlier fixed-address test macro, raw-ROM pointers and actual
dimension-bank addresses are separate. The incoming real .old register is t. -/
def initDimensionBank (dimensions : Nat → Nat) : List PackingOp :=
  [.base (.base (.constant .address (dimensions 0))),
   .base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .value .index)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address (dimensions 1))),
   .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .value .index)),
   .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address (dimensions 2))),
   .base (.base (.storeHeap .address .old))]

theorem initDimensionBank_length (dimensions : Nat → Nat) :
    (initDimensionBank dimensions).length = 10 := rfl

theorem initDimensionBank_straight (dimensions : Nat → Nat) :
    StraightProgram (initDimensionBank dimensions) := by
  simp [initDimensionBank, StraightProgram, StraightOp]

theorem initDimensionBank_heap (rom : PhysicalROM) (dimensions : Nat → Nat)
    (state : WordState bits) :
    (executeOps rom (initDimensionBank dimensions) state).heap =
      Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (dimensions 0))
            (BitVec.ofNat bits (rom.input.getD (BitVec.ofNat bits 0).toNat 0)))
          (BitVec.ofNat bits (dimensions 1))
            (BitVec.ofNat bits (rom.input.getD (BitVec.ofNat bits 1).toNat 0)))
        (BitVec.ofNat bits (dimensions 2)) (state.register .old) := by
  simp [initDimensionBank, executeOps, packingExecuteOp, wordOp, wordInstruction,
    PhysicalROM.words]

theorem initDimensionBank_prefix_frame (rom : PhysicalROM) (dimensions : Nat → Nat)
    (point : BitVec bits)
    (outside : ∀ index < 3, point ≠ BitVec.ofNat bits (dimensions index)) :
    WordPrefixFrame rom (initDimensionBank dimensions) point := by
  intro state count
  have h0 := outside 0 (by omega)
  have h1 := outside 1 (by omega)
  have h2 := outside 2 (by omega)
  by_cases hc : count ≤ 10
  · interval_cases count <;>
      simp [initDimensionBank, executeOps, packingExecuteOp, wordOp, wordInstruction,
        Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]
  · rw [List.take_of_length_le (by rw [initDimensionBank_length]; omega),
      initDimensionBank_heap, Function.update_of_ne h2, Function.update_of_ne h1,
      Function.update_of_ne h0]

theorem initDimensionBank_access (rom : PhysicalROM) (dimensions : Nat → Nat)
    (state : WordState bits) (heapWords count : Nat) (hrom : 2 ≤ rom.input.length)
    (hbank : ∀ index < 3, dimensions index < heapWords) (hc : count < 10) :
    packingAccessFits rom heapWords
      (executeOps rom ((initDimensionBank dimensions).take count) state)
      ((initDimensionBank dimensions)[count]'(by simpa only [initDimensionBank_length] using hc)) := by
  have h1 : 1 % 2 ^ bits ≤ 1 := Nat.mod_le _ _
  have h0b : dimensions 0 % 2 ^ bits < heapWords :=
    lt_of_le_of_lt (Nat.mod_le _ _) (hbank 0 (by omega))
  have h1b : dimensions 1 % 2 ^ bits < heapWords :=
    lt_of_le_of_lt (Nat.mod_le _ _) (hbank 1 (by omega))
  have h2b : dimensions 2 % 2 ^ bits < heapWords :=
    lt_of_le_of_lt (Nat.mod_le _ _) (hbank 2 (by omega))
  interval_cases count <;>
    simp [initDimensionBank, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, PhysicalROM.words, BitVec.toNat_ofNat] <;> omega

def dynamicConstant (dimensions : Nat → Nat) (stack : Nat)
    (bank : Register → Nat) (target : Register) (expr : Expr) : List PackingOp :=
  (localizeExpr dimensions expr).compile stack ++ writeControl (bank target)

theorem dynamicConstant_length (dimensions : Nat → Nat) (stack : Nat)
    (bank : Register → Nat) (target : Register) (expr : Expr) :
    (dynamicConstant dimensions stack bank target expr).length ≤ 5 * expr.size + 2 := by
  have hh := Expr.compile_length_le (localizeExpr dimensions expr) stack
  rw [expr_localize_size] at hh
  simpa only [dynamicConstant, List.length_append, writeControl_length] using
    Nat.add_le_add_right hh 2

theorem dynamicConstant_straight (dimensions : Nat → Nat) (stack : Nat)
    (bank : Register → Nat) (target : Register) (expr : Expr) :
    StraightProgram (dynamicConstant dimensions stack bank target expr) := by
  intro op hm
  rcases List.mem_append.mp hm with hm | hm
  · exact Expr.compile_noJump (localizeExpr dimensions expr) stack op hm
  · exact writeControl_straight (bank target) op hm

theorem dynamicConstant_prefix_frame (rom : PhysicalROM) (dimensions : Nat → Nat)
    (stack : Nat) (bank : Register → Nat) (target : Register) (expr : Expr)
    (point : BitVec bits) (ht : point ≠ BitVec.ofNat bits (bank target))
    (outside : ∀ address, stack ≤ address → address < stack + expr.size →
      point ≠ BitVec.ofNat bits address) :
    WordPrefixFrame rom (dynamicConstant dimensions stack bank target expr) point := by
  apply wordPrefixFrame_append
  · apply expr_compile_word_prefix_frame
    simpa only [expr_localize_size] using outside
  · exact fun state count => writeControl_prefix_frame rom _ count state point ht

theorem dynamicConstant_nat_heap (dimensions : Nat → Nat) (stack : Nat)
    (bank : Register → Nat) (target : Register) (expr : Expr) (bound : Nat)
    (hb : exprInputsBelow bound expr) (hf : expr.Below stack)
    (hd : ∀ address < bound, dimensions address < stack)
    (source physical : PhysicalROM) (state : NatState)
    (hreal : ∀ address < bound, state.heap (dimensions address) = source.semantic.read .input address) :
    (runOps physical (dynamicConstant dimensions stack bank target expr) state).heap =
      Function.update
        (runOps physical ((localizeExpr dimensions expr).compile stack) state).heap
        (bank target) (expr.eval source state.heap) := by
  rw [dynamicConstant, runOps_append]
  change Function.update
    (runOps physical ((localizeExpr dimensions expr).compile stack) state).heap (bank target)
    ((runOps physical ((localizeExpr dimensions expr).compile stack) state).register .value) = _
  rw [localized_compile_value expr dimensions bound stack hb hf hd source physical state hreal]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
