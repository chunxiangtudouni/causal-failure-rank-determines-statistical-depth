module

public import Structure.PSTR_BuildLower_ValueStep_042
public import Structure.PSTR_BuildLower_ASTExprBounds_035

/-! Actual dynamic constants update the one real VM register word. Other
VM words and the source heap are protected from Expr temporaries; exact
original Nat immediates follow the proved Expr-node bounds, not a new input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DynamicStep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

def code (target : Register) (expr : Expr) : List PackingOp :=
  fixedExprCode expr ++ relativeWrite (registerOffset target)

theorem code_length (target : Register) (expr : Expr) : (code target expr).length ≤ 7 * expr.size + 3 := by
  have hh := fixedExprCode_length expr
  simpa only [code, List.length_append, relativeWrite_length] using Nat.add_le_add_right hh 3

theorem code_straight (target : Register) (expr : Expr) : StraightProgram (code target expr) := by
  intro op hm
  rcases List.mem_append.mp hm with he | hw
  · exact bankCompile_noJump _ 128 op he
  · exact relativeWrite_straight _ op hw

private theorem expr_base (expr : Expr) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (fixedExprCode expr) state).register .address = state.register .address := by
  have hh := (bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) rom 128).1 state (fixedExprCode expr).length
  change (executeOps rom ((fixedExprCode expr).take (fixedExprCode expr).length) state).register .address = _ at hh
  simpa only [List.take_length] using hh

private theorem expr_VM (expr : Expr) (rom : PhysicalROM) (state : WordState bits)
    (ht : 128 + expr.size ≤ 2 ^ bits) :
    portRegisters (state.register .address) (executeOps rom (fixedExprCode expr) state).heap =
      portRegisters (state.register .address) state.heap := by
  funext reg
  exact bankCompile_word_read_below (relocateExpr (dimensionBank 0) (variableBank 0) expr) rom 128 state (registerOffset reg)
    ((registerSlot_bounds reg).2.trans (by decide : 39 < 128))
    (by simpa only [relocateExpr_size] using ht)

theorem execute_VM (target : Register) (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM) (environment : Nat → BitVec bits)
    (state : WordState bits) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0)) :
    portRegisters (state.register .address) (executeOps physical (code target expr) state).heap =
      Function.update (portRegisters (state.register .address) state.heap) target (exprWordEval source environment expr) := by
  have hb : 6 ≤ bits := by
    by_contra hn
    have hh : 2 ^ bits ≤ 32 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : bits ≤ 5)
    omega
  rw [code, executeOps_append, relativeWrite_heap, expr_base, portRegisters_update _ (ValueStep.bank_injective _ hb),
    fixedExprCode_word_direct expr hc hd source physical environment state ht hcell hdim, expr_VM expr physical state ht]

theorem run (target : Register) (expr : Expr) (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code target expr ++ right).length)) :
    packingRun rom (left ++ code target expr ++ right) (code target expr).length state =
      executeOps rom (code target expr) state := by
  apply PSTRWordSegments.straight_segment rom _ _ left.length
    (by simp only [List.length_append]; omega)
    (PA17UniformGenerator035a.segment_index left (code target expr) right) (code_straight target expr) hcode hpcfit state hpc ha

theorem call_nat_VM (target : Register) (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM) (environment : Nat → Nat)
    (state : WordState bits) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = BitVec.ofNat bits (environment address))
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0))
    (hvalues : ExprBounds.nodesFit bits source environment expr)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code target expr ++ right).length)) :
    portRegisters (state.register .address)
      (packingRun physical (left ++ code target expr ++ right) (code target expr).length state).heap =
      Function.update (portRegisters (state.register .address) state.heap) target (BitVec.ofNat bits (expr.eval source environment)) := by
  rw [run target expr physical left right state hpc ha hcode hpcfit,
    execute_VM target expr hc hd source physical (fun address => BitVec.ofNat bits (environment address)) state ht hcell hdim,
    ExprBounds.wordEval_exact bits expr source environment hvalues (by intro address h; dsimp only [Fits]; omega)]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DynamicStep
