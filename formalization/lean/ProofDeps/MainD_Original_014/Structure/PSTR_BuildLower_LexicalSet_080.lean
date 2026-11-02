module

public import Structure.PSTR_BuildLower_LexicalRange_079
public import Structure.PSTR_BuildLower_RuntimeFields_065
public import Structure.PSTR_BuildLower_ASTExprBounds_035

/-! A loop bound is computed by the real inline expression instructions and
stored in its real counter cell. Original Expr-node bounds justify only the
expression's Nat value, while the backend retains direct Word semantics. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.LexicalSet
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b PA17ProgramTemplates041

def code (counter : Nat) (expr : Expr) : List PackingOp := fixedExprCode expr ++ relativeWrite (64 + counter)

theorem code_straight (counter : Nat) (expr : Expr) : StraightProgram (code counter expr) := by
  intro op hm
  rcases List.mem_append.mp hm with he | hw
  · exact bankCompile_noJump _ 128 op he
  · exact relativeWrite_straight _ op hw

theorem code_range {q : Nat} {full : List (Finset (Fin q))}
    (physical : PhysicalROM) (counter : Nat) (expr : Expr) (hc : counter < 21) :
    BankRangeFrame (bits := bits q full) physical (code counter expr) 64 (128 + expr.size) := by
  apply bankRangeFrame_append
  · apply bankRangeFrame_mono physical _ 128 (128 + expr.size) 64 (128 + expr.size) (by decide) le_rfl
    simpa only [fixedExprCode, relocateExpr_size] using
      bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128
  · exact ViewFrame.relativeWrite_range physical (64 + counter) _ _ (by omega) (by omega)

theorem prefix_offset {wordBits : Nat} (physical : PhysicalROM) (counter : Nat) (hc : counter < 21)
    (expr : Expr) (offset : Nat) (hoff : offset < 128) (hne : offset ≠ 64 + counter)
    (ht : 128 + expr.size ≤ 2 ^ wordBits) (state : WordState wordBits) (count : Nat) :
    (executeOps physical ((code counter expr).take count) state).heap
      (state.register .address + BitVec.ofNat _ offset) = state.heap (state.register .address + BitVec.ofNat _ offset) := by
  have exprFrame : BankRangeFrame (bits := wordBits) physical (fixedExprCode expr) 128 (128 + expr.size) := by
    simpa only [fixedExprCode, relocateExpr_size] using
      bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128
  let middle := executeOps physical ((fixedExprCode expr).take count) state
  have middleBase : middle.register .address = state.register .address := exprFrame.1 state count
  have offsetFit : Fits wordBits offset := by change offset < 2 ^ wordBits; omega
  have counterFit : Fits wordBits (64 + counter) := by change 64 + counter < 2 ^ wordBits; omega
  have middleHeap := ControlDataFrame.range_offset physical (fixedExprCode expr) 128 (128 + expr.size)
    exprFrame ht offset offsetFit (Or.inl hoff) state count
  have tail := relativeWrite_prefix_frame physical (64 + counter) middle
    (state.register .address + BitVec.ofNat _ offset)
    (by rw [middleBase]; exact ControlDataFrame.offset_ne _ _ _ offsetFit counterFit hne)
    (count - (fixedExprCode expr).length)
  rw [code, List.take_append, executeOps_append]
  exact tail.trans middleHeap

theorem actual_prefix_offset {wordBits : Nat} (physical : PhysicalROM) (counter : Nat) (hc : counter < 21)
    (expr : Expr) (offset : Nat) (hoff : offset < 128) (hne : offset ≠ 64 + counter)
    (ht : 128 + expr.size ≤ 2 ^ wordBits) (state : WordState wordBits) (left right : List PackingOp)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit wordBits (packingCode (left ++ code counter expr ++ right)))
    (hpcfit : Fits wordBits (5 * (left ++ code counter expr ++ right).length)) (count : Nat) (hn : count ≤ (code counter expr).length) :
    (packingRun physical (left ++ code counter expr ++ right) count state).heap
      (state.register .address + BitVec.ofNat _ offset) = state.heap (state.register .address + BitVec.ofNat _ offset) := by
  rw [SourceRep.straight_prefix physical left (code counter expr) right state (code_straight counter expr) hcode hpcfit hpc ha count hn]
  exact prefix_offset physical counter hc expr offset hoff hne ht state count

theorem run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (physical : PhysicalROM)
    (counter : Nat) (hcounter : counter < 21) (expr : Expr) (environment : Nat → Nat)
    (hc : expressionCellLimit expr ≤ 21) (hd : expressionInputLimit expr ≤ 3) (hs : expr.size ≤ 29)
    (logical : State) (state : WordState (bits q full)) (hrep : SourceRep.Prepared q full logical state)
    (data : RuntimeData.Data q full state.heap)
    (henv : ∀ address < 21, state.heap (state.register .address + BitVec.ofNat _ (64 + address)) = BitVec.ofNat _ (environment address))
    (hvalues : ExprBounds.nodesFit (bits q full) (dimensionROM full.length q (t q full)) environment expr)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ code counter expr ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ code counter expr ++ right).length)) :
    let after := packingRun physical (left ++ code counter expr ++ right) (code counter expr).length state
    (code counter expr).length ≤ 206 ∧ SourceRep.Prepared q full logical after ∧ RuntimeData.Data q full after.heap ∧
      after.pc = BitVec.ofNat _ (5 * (left.length + (code counter expr).length)) ∧ after.halted = false ∧
      ∀ address < 21, after.heap (after.register .address + BitVec.ofNat _ (64 + address)) =
        BitVec.ofNat _ (Function.update environment counter (expr.eval (dimensionROM full.length q (t q full)) environment) address) := by
  have hr := SourceRep.straight_prefix physical left (code counter expr) right state (code_straight counter expr)
    hcode hpcfit hpc ha (code counter expr).length le_rfl
  rw [List.take_length] at hr
  have hf := code_range (q := q) (full := full) physical counter expr hcounter
  have preserved := SourceRep.lexical_range_data q full hq physical (code counter expr) 64 (128 + expr.size)
    (by decide) (by omega) (by omega) hf logical state hrep data (code counter expr).length
  rw [List.take_length] at preserved
  have ht : 128 + expr.size ≤ 2 ^ bits q full := by
    have hh := bank_offset_fits q full hq (128 + expr.size) (by omega)
    change controlBase q full + (128 + expr.size) < 2 ^ bits q full at hh
    omega
  have value := fixedExprCode_word_direct expr (by omega) hd (dimensionROM full.length q (t q full)) physical
    (fun address => BitVec.ofNat _ (environment address)) state ht
    (by intro address had; exact henv address (had.trans_le hc))
    (by intro address had; exact RuntimeData.Data.dimensions q full state data hrep.address address (had.trans_le hd))
  rw [ExprBounds.wordEval_exact _ expr _ environment hvalues
    (by intro address had; have hb := bits_room q full; change address < 2 ^ bits q full; omega)] at value
  have exprBase : (executeOps physical (fixedExprCode expr) state).register .address = state.register .address := by
    have hh := (bankCompile_word_frame (bits := bits q full)
      (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128).1 state (fixedExprCode expr).length
    simpa only [fixedExprCode, List.take_length] using hh
  have blockBase : (executeOps physical (code counter expr) state).register .address = state.register .address := by
    simpa only [List.take_length] using hf.1 state (code counter expr).length
  dsimp only
  rw [hr]
  refine ⟨?_, preserved.1, preserved.2, ?_, (executeOps_halted physical _ state).trans ha, ?_⟩
  · have hh := fixedExprCode_length expr
    simp only [code, List.length_append, relativeWrite_length]
    omega
  · rw [executeOps_pc physical _ state (code_straight counter expr), hpc, BitVec.ofNat_add_ofNat]
    congr 1; omega
  · intro address had
    rw [blockBase, code, executeOps_append, relativeWrite_heap, exprBase, value]
    by_cases he : address = counter
    · subst address
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (ControlDataFrame.offset_ne _ _ _
        (by change 64 + address < 2 ^ bits q full; omega)
        (by change 64 + counter < 2 ^ bits q full; omega) (by omega)), Function.update_of_ne he]
      have hh := bankCompile_word_read_below (relocateExpr (dimensionBank 0) (variableBank 0) expr)
        physical 128 state (64 + address) (by omega) (by simpa only [relocateExpr_size] using ht)
      exact hh.trans (henv address had)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.LexicalSet

