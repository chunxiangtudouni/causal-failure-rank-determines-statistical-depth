module

public import Structure.PSTR_BuildLower_BankExpr_009

/-! The source AST's fixed expressions execute from real bank cells. The
dimension ROM is used only in the mathematical value specification, never as
an actual expression input. Word refinement keeps its exact prefix obligations
internal, to be discharged by the constructed full run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b

theorem bankCompile_noJump (expr : Expr) (stack : Nat) :
    ∀ op ∈ bankCompile stack expr, NoJump op := by
  induction expr generalizing stack with
  | constant value => simp [bankCompile, NoJump]
  | cell address => simp [bankCompile, relativeRead, NoJump]
  | input address => simp [bankCompile, NoJump]
  | binary operation left right ihl ihr =>
    intro op hm
    simp only [bankCompile, List.mem_append] at hm
    rcases hm with hm | hm | hm | hm
    · exact ihl stack op hm
    · have hh : ∀ entry ∈ relativeWrite stack, NoJump entry := by
        simp [relativeWrite, NoJump]
      exact hh op hm
    · exact ihr (stack + 1) op hm
    · have hh : ∀ entry ∈ bankFinish stack operation, NoJump entry := by
        cases operation <;> simp [bankFinish, Binary.instruction, NoJump]
      exact hh op hm

theorem bankCompile_segment_run (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false) :
    natRun rom (left ++ bankCompile stack expr ++ right) (bankCompile stack expr).length state =
      runOps rom (bankCompile stack expr) state := by
  exact natRun_of_straight_segment rom _ _ left.length
    (by simp only [List.length_append]; omega)
    (segment_index left (bankCompile stack expr) right) (bankCompile_noJump expr stack) state hpc ha

theorem bankCompile_word_segment (expr : Expr) (rom : PhysicalROM) (stack bits : Nat)
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ bankCompile stack expr ++ right)))
    (hsafe : ∀ count < (bankCompile stack expr).length,
      RegistersFit bits (natRun rom (left ++ bankCompile stack expr ++ right) count state) ∧
        Fits bits (natRun rom (left ++ bankCompile stack expr ++ right) count state).pc) :
    packingRun rom (left ++ bankCompile stack expr ++ right) (bankCompile stack expr).length
      (state.toWord bits) = (runOps rom (bankCompile stack expr) state).toWord bits := by
  rw [natRun_toWord _ _ _ _ hcode hsafe, bankCompile_segment_run expr rom stack left right state hpc ha]

def fixedExprCode (expr : Expr) : List PackingOp :=
  bankCompile 128 (relocateExpr (dimensionBank 0) (variableBank 0) expr)

theorem fixedExprCode_length (expr : Expr) : (fixedExprCode expr).length ≤ 7 * expr.size := by
  simpa only [fixedExprCode, relocateExpr_size] using
    bankCompile_length (relocateExpr (dimensionBank 0) (variableBank 0) expr) 128

theorem fixedExprCode_value (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM)
    (environment : Nat → Nat) (state : NatState)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + 64 + address) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + address) = source.semantic.read .input address) :
    (runOps physical (fixedExprCode expr) state).register .value = expr.eval source environment := by
  have hh : (relocateExpr (dimensionBank 0) (variableBank 0) expr).Below 128 := by
    simpa only [expressionStack, Nat.zero_add] using relocated_bank_below expr 0 hc hd
  rw [fixedExprCode, (bankCompile_correct _ physical 128 hh state).1]
  apply relocateExpr_eval
  · intro address ha
    simpa only [variableBank, Nat.zero_add, Nat.add_assoc] using hcell address ha
  · intro address ha
    simpa only [dimensionBank, Nat.zero_add] using hdim address ha

theorem fixedExprCode_word_value (expr : Expr) (hc : expressionCellLimit expr ≤ 22)
    (hd : expressionInputLimit expr ≤ 3) (source physical : PhysicalROM)
    (environment : Nat → Nat) (bits : Nat) (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (ha : state.halted = false)
    (hcell : ∀ address < expressionCellLimit expr,
      state.heap (state.register .address + 64 + address) = environment address)
    (hdim : ∀ address < expressionInputLimit expr,
      state.heap (state.register .address + address) = source.semantic.read .input address)
    (hcode : WordsFit bits (packingCode (left ++ fixedExprCode expr ++ right)))
    (hsafe : ∀ count < (fixedExprCode expr).length,
      RegistersFit bits (natRun physical (left ++ fixedExprCode expr ++ right) count state) ∧
        Fits bits (natRun physical (left ++ fixedExprCode expr ++ right) count state).pc)
    (hvalue : Fits bits (expr.eval source environment)) :
    ((packingRun physical (left ++ fixedExprCode expr ++ right) (fixedExprCode expr).length
      (state.toWord bits)).register .value).toNat = expr.eval source environment := by
  have hrun : packingRun physical (left ++ fixedExprCode expr ++ right) (fixedExprCode expr).length
      (state.toWord bits) = (runOps physical (fixedExprCode expr) state).toWord bits :=
    bankCompile_word_segment _ physical 128 bits left right state hpc ha hcode hsafe
  rw [hrun]
  change (BitVec.ofNat bits ((runOps physical (fixedExprCode expr) state).register .value)).toNat = _
  rw [fixedExprCode_value expr hc hd source physical environment state hcell hdim,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
