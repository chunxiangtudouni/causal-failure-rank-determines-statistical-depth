module

public import Structure.PSTR_BuildLower_ValueAccess_117
public import Structure.PSTR_BuildLower_TraceAccess_119
public import Structure.PSTR_BuildLower_DynamicStep_043

/-! Concrete inline arithmetic and dynamic immediate segments satisfy real
proper-clock access. Only their static source shape and actual CB are used;
their source-value correctness remains the independently proved simulation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034 PA17UniformGenerator035b

theorem dynamic_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (expr : Expr)
    (hc : expressionCellLimit expr ≤ 21) (hi : expressionInputLimit expr ≤ 3) (hs : expr.size ≤ 29)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    PackedAccessSafe (allocated q full) physical (DynamicStep.code target expr) state := by
  change PackedAccessSafe (allocated q full) physical (fixedExprCode expr ++ relativeWrite (registerOffset target)) state
  apply PackedAccessSafe.append _ _ _ _ state (fixed_safe q full hq physical expr hc hi hs state base)
  apply write_safe
  have afterBase : (executeOps physical (fixedExprCode expr) state).register .address = state.register .address := by
    have hh := (bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128).1
      state (fixedExprCode expr).length
    change (executeOps physical ((fixedExprCode expr).take (fixedExprCode expr).length) state).register .address = _ at hh
    simpa only [List.take_length] using hh
  rw [afterBase]
  exact point_room q full hq state base (registerOffset target)
    (by have hh := registerSlot_bounds target; change 32 ≤ registerOffset target ∧ registerOffset target < 39 at hh; omega)

theorem copy_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (source target : Nat) (hsource : source ≤ 512) (htarget : target ≤ 512)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    PackedAccessSafe (allocated q full) physical (relativeCopy source target) state := by
  change PackedAccessSafe (allocated q full) physical (relativeRead source .value ++ relativeWrite target) state
  apply PackedAccessSafe.append _ _ _ _ state
    (read_safe physical source (allocated q full) .value state (point_room q full hq state base source hsource))
  apply write_safe
  change (state.register .address + BitVec.ofNat _ target).toNat < allocated q full
  exact point_room q full hq state base target htarget

theorem value_actual_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (op : ValueOp) (left right : List PackingOp) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ op.relativeLower ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ op.relativeLower ++ right) state op.relativeLower.length :=
  TraceAccess.straight physical left op.relativeLower right (allocated q full) state (relativeValue_straight op)
    (value_fixed_safe q full hq op physical state base) hpc ha hcode hpcfit

theorem dynamic_actual_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (expr : Expr)
    (hc : expressionCellLimit expr ≤ 21) (hi : expressionInputLimit expr ≤ 3) (hs : expr.size ≤ 29)
    (left right : List PackingOp) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DynamicStep.code target expr ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ DynamicStep.code target expr ++ right)
      state (DynamicStep.code target expr).length :=
  TraceAccess.straight physical left (DynamicStep.code target expr) right (allocated q full) state
    (DynamicStep.code_straight target expr) (dynamic_safe q full hq physical target expr hc hi hs state base) hpc ha hcode hpcfit

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
