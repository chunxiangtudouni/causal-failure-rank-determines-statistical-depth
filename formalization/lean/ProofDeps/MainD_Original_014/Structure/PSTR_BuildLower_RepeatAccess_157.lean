module

public import Structure.PSTR_BuildLower_InlineAccess_120
public import Structure.PSTR_BuildLower_LoopFrames_091

/-! Real save/Expr/counter-write and real restore6 accesses. Finite bank
room and the fixed Expr compiler discharge all primitive obligations; no
whole-AST safety or whole-body Nat-register premise is accepted. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.RepeatAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open PA17UniformGenerator035b

theorem setup_local_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter saved : Nat) (hc : counter ≤ 512) (hd : saved ≤ 512)
    (expr : Expr) (cells : expressionCellLimit expr ≤ 21) (inputs : expressionInputLimit expr ≤ 3) (size : expr.size ≤ 29)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    PA17PackedTranslator034.PackedAccessSafe (allocated q full) physical (relativeRepeatPrefix counter saved expr) state := by
  rw [relativeRepeatPrefix, List.append_assoc]
  apply PA17PackedTranslator034.PackedAccessSafe.append _ _ _ _ state
    (BankAccess.copy_safe q full hq physical counter saved hc hd state base)
  let middle := executeOps physical (relativeCopy counter saved) state
  have middleBase : middle.register .address = BitVec.ofNat _ (controlBase q full) := by
    have hh := relativeCopy_base_prefix physical counter saved state (relativeCopy counter saved).length
    rw [List.take_length] at hh
    exact hh.trans base
  apply PA17PackedTranslator034.PackedAccessSafe.append _ _ _ _ middle
    (BankAccess.fixed_safe q full hq physical expr cells inputs size middle middleBase)
  apply BankAccess.write_safe
  have finalBase : (executeOps physical (fixedExprCode expr) middle).register .address = middle.register .address := by
    have hh := (bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128).1
      middle (fixedExprCode expr).length
    change (executeOps physical ((fixedExprCode expr).take (fixedExprCode expr).length) middle).register .address = _ at hh
    simpa only [List.take_length] using hh
  rw [finalBase]
  exact BankAccess.point_room q full hq middle middleBase counter hc

theorem setup_actual_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (counter saved : Nat) (hc : counter ≤ 512) (hd : saved ≤ 512)
    (expr : Expr) (cells : expressionCellLimit expr ≤ 21) (inputs : expressionInputLimit expr ≤ 3) (size : expr.size ≤ 29)
    (left right : List PackingOp) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeRepeatPrefix counter saved expr ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeRepeatPrefix counter saved expr ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ relativeRepeatPrefix counter saved expr ++ right) state
      (relativeRepeatPrefix counter saved expr).length :=
  TraceAccess.straight physical left _ right (allocated q full) state (LoopFrames.setup_straight _ _ _)
    (setup_local_safe q full hq physical counter saved hc hd expr cells inputs size state base) hpc ha hcode hpcfit

theorem restore_actual_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (source target : Nat) (hc : source ≤ 512) (hd : target ≤ 512)
    (left right : List PackingOp) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeCopy source target ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeCopy source target ++ right).length)) :
    TraceAccess.Safe (allocated q full) physical (left ++ relativeCopy source target ++ right) state 6 := by
  have result := TraceAccess.straight physical left _ right (allocated q full) state (SourceRep.copy_straight _ _)
    (BankAccess.copy_safe q full hq physical source target hc hd state base) hpc ha hcode hpcfit
  rwa [relativeCopy_length] at result

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.RepeatAccess
