module

public import Structure.PSTR_BuildLower_ExprWord_025
public import Structure.PSTR_BuildLower_AST_014

/-! Relative-bank dynamic constants execute the original typed expression
with direct Word semantics, using real dimension/counter bank loads. These
are internal representation equations, not original caller qualifications. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

theorem relocateExpr_word_eval (expr : Expr) (dimensions cellMap : Nat → Nat)
    (source physical : PhysicalROM) (environment heap : Nat → BitVec bits)
    (hc : ∀ address < expressionCellLimit expr, heap (cellMap address) = environment address)
    (hd : ∀ address < expressionInputLimit expr,
      heap (dimensions address) = BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0)) :
    exprWordEval physical heap (relocateExpr dimensions cellMap expr) = exprWordEval source environment expr := by
  induction expr with
  | constant value => rfl
  | cell address => exact hc address (by simp [expressionCellLimit])
  | input address => exact hd address (by simp [expressionInputLimit])
  | binary op left right ihl ihr =>
    have hcl : ∀ address < expressionCellLimit left, heap (cellMap address) = environment address :=
      fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    have hcr : ∀ address < expressionCellLimit right, heap (cellMap address) = environment address :=
      fun address ha => hc address (lt_of_lt_of_le ha (Nat.le_max_right _ _))
    have hdl : ∀ address < expressionInputLimit left,
        heap (dimensions address) = BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0) :=
      fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_left _ _))
    have hdr : ∀ address < expressionInputLimit right,
        heap (dimensions address) = BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0) :=
      fun address ha => hd address (lt_of_lt_of_le ha (Nat.le_max_right _ _))
    simp only [relocateExpr, exprWordEval, ihl hcl hdl, ihr hcr hdr]

theorem fixedExprCode_word_direct (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM)
    (environment : Nat → BitVec bits) (state : WordState bits)
    (ht : 128 + expr.size ≤ 2 ^ bits)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0)) :
    (executeOps physical (fixedExprCode expr) state).register .value = exprWordEval source environment expr := by
  have hh : (relocateExpr (dimensionBank 0) (variableBank 0) expr).Below 128 := by
    simpa only [expressionStack, Nat.zero_add] using relocated_bank_below expr 0 hc hd
  rw [fixedExprCode, bankCompile_word_value _ physical 128 hh
    (by simpa only [relocateExpr_size] using ht) state]
  apply relocateExpr_word_eval
  · intro address ha
    simpa only [variableBank, Nat.zero_add] using hcell address ha
  · intro address ha
    simpa only [dimensionBank, Nat.zero_add] using hdim address ha

theorem fixedExprCode_word_actual (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM)
    (environment : Nat → BitVec bits) (left right : List PackingOp) (state : WordState bits)
    (ht : 128 + expr.size ≤ 2 ^ bits)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ fixedExprCode expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ fixedExprCode expr ++ right).length)) :
    ((packingRun physical (left ++ fixedExprCode expr ++ right) (fixedExprCode expr).length state).register .value) =
      exprWordEval source environment expr := by
  have hrun : packingRun physical (left ++ fixedExprCode expr ++ right) (fixedExprCode expr).length state =
      executeOps physical (fixedExprCode expr) state :=
    bankCompile_word_run _ physical 128 left right state hpc ha hcode hpcfit
  rw [hrun]
  exact fixedExprCode_word_direct expr hc hd source physical environment state ht hcell hdim

theorem dynamic_word_heap (ports : BuilderPorts) (start : Nat) (target : Register)
    (expr : Expr) (hc : expressionCellLimit expr ≤ 22) (hd : expressionInputLimit expr ≤ 3)
    (source physical : PhysicalROM) (environment : Nat → BitVec bits) (state : WordState bits)
    (ht : 128 + expr.size ≤ 2 ^ bits)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits (64 + address)) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + BitVec.ofNat bits address) =
        BitVec.ofNat bits ((source.words .input).getD (BitVec.ofNat bits address).toNat 0)) :
    (executeOps physical (lowerOpExpr ports start (.constant target expr)) state).heap =
      Function.update (executeOps physical (fixedExprCode expr) state).heap
        (state.register .address + BitVec.ofNat bits (registerOffset target))
        (exprWordEval source environment expr) := by
  have hv := fixedExprCode_word_direct expr hc hd source physical environment state ht hcell hdim
  have hb := (bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr)
    physical 128).1 state (fixedExprCode expr).length
  change (executeOps physical ((fixedExprCode expr).take (fixedExprCode expr).length) state).register .address = _ at hb
  rw [List.take_length] at hb
  rw [lowerOpExpr_dynamic, executeOps_append, relativeWrite_heap, hv, hb]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
