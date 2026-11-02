module

public import Structure.PSTR_BuildLower_SourceRep_048

/-! Fine control-bank frames needed by structured source induction. In
particular Expr temporaries do not overwrite lexical counters or saved loop
words between the VM and stack. A single large enclosing interval would lose
that necessary fact, so the actual write regions are kept separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlDataFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PA17UniformGenerator035b
variable {bits : Nat}

theorem offset_ne (base : BitVec bits) (left right : Nat)
    (hl : Fits bits left) (hr : Fits bits right) (hne : left ≠ right) :
    base + BitVec.ofNat bits left ≠ base + BitVec.ofNat bits right := by
  intro hh
  have he := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp hh)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] at he
  exact hne he

theorem range_offset (rom : PhysicalROM) (code : List PackingOp) (lo hi : Nat)
    (hf : BankRangeFrame (bits := bits) rom code lo hi) (hhi : hi ≤ 2 ^ bits)
    (offset : Nat) (hoff : Fits bits offset) (outside : offset < lo ∨ hi ≤ offset)
    (state : WordState bits) (count : Nat) :
    (executeOps rom (code.take count) state).heap (state.register .address + BitVec.ofNat bits offset) =
      state.heap (state.register .address + BitVec.ofNat bits offset) := by
  apply hf.2
  intro changed hl hh
  exact offset_ne _ offset changed hoff (hh.trans_le hhi) (by rcases outside with h | h <;> omega)

theorem straight_range_offset (rom : PhysicalROM) (left block right : List PackingOp) (lo hi : Nat)
    (hf : BankRangeFrame (bits := bits) rom block lo hi) (hhi : hi ≤ 2 ^ bits)
    (offset : Nat) (hoff : Fits bits offset) (outside : offset < lo ∨ hi ≤ offset)
    (state : WordState bits) (hs : StraightProgram block)
    (hcode : WordsFit bits (packingCode (left ++ block ++ right)))
    (hpcfit : Fits bits (5 * (left ++ block ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ block.length) :
    (packingRun rom (left ++ block ++ right) count state).heap (state.register .address + BitVec.ofNat bits offset) =
      state.heap (state.register .address + BitVec.ofNat bits offset) := by
  rw [SourceRep.straight_prefix rom left block right state hs hcode hpcfit hpc ha count hc]
  exact range_offset rom block lo hi hf hhi offset hoff outside state count

theorem dynamic_offset (rom : PhysicalROM) (target : Register) (expr : Expr)
    (offset : Nat) (hoff : Fits bits offset) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hvm : offset ≠ registerOffset target) (outside : offset < 128 ∨ 128 + expr.size ≤ offset)
    (state : WordState bits) :
    (executeOps rom (DynamicStep.code target expr) state).heap (state.register .address + BitVec.ofNat bits offset) =
      state.heap (state.register .address + BitVec.ofNat bits offset) := by
  have exprFrame : BankRangeFrame (bits := bits) rom (fixedExprCode expr) 128 (128 + expr.size) := by
    simpa only [fixedExprCode, relocateExpr_size] using
      bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) rom 128
  have exprBase : (executeOps rom (fixedExprCode expr) state).register .address = state.register .address := by
    simpa only [List.take_length] using exprFrame.1 state (fixedExprCode expr).length
  have htarget : Fits bits (registerOffset target) := by
    have hh := (registerSlot_bounds target).2
    change registerOffset target < 39 at hh
    change registerOffset target < 2 ^ bits
    omega
  rw [DynamicStep.code, executeOps_append, relativeWrite_heap, exprBase,
    Function.update_of_ne (offset_ne _ _ _ hoff htarget hvm)]
  have he := range_offset rom (fixedExprCode expr) 128 (128 + expr.size) exprFrame ht offset hoff outside state
    (fixedExprCode expr).length
  simpa only [List.take_length] using he

theorem dynamic_actual_offset (rom : PhysicalROM) (left right : List PackingOp) (target : Register) (expr : Expr)
    (offset : Nat) (hoff : Fits bits offset) (ht : 128 + expr.size ≤ 2 ^ bits)
    (hvm : offset ≠ registerOffset target) (outside : offset < 128 ∨ 128 + expr.size ≤ offset)
    (state : WordState bits)
    (hcode : WordsFit bits (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits bits (5 * (left ++ DynamicStep.code target expr ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    (packingRun rom (left ++ DynamicStep.code target expr ++ right) (DynamicStep.code target expr).length state).heap
      (state.register .address + BitVec.ofNat bits offset) = state.heap (state.register .address + BitVec.ofNat bits offset) := by
  rw [DynamicStep.run target expr rom left right state hpc ha hcode hpcfit]
  exact dynamic_offset rom target expr offset hoff ht hvm outside state

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ControlDataFrame
