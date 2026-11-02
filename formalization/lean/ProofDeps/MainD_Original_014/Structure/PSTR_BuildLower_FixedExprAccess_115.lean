module

public import Structure.PSTR_BuildLower_BankAccess_114
public import Structure.PSTR_BuildLower_PreparedLayout_054

/-! The fixed Expr port reads only the genuine dimension/lexical bank and
writes its reserved temporaries. Original static shape and the real CB room
discharge every direct Word primitive access, with no caller numeric oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034 PA17UniformGenerator035b

theorem cell_limit_of_below (expr : Expr) (limit : Nat) (below : expr.Below limit) :
    expressionCellLimit expr ≤ limit := by
  induction expr with
  | constant value => exact Nat.zero_le _
  | cell address => exact Nat.succ_le_of_lt below
  | input address => exact Nat.zero_le _
  | binary operation left right ihLeft ihRight =>
    have hleft := ihLeft below.1
    have hright := ihRight below.2
    change max (expressionCellLimit left) (expressionCellLimit right) ≤ limit
    omega

theorem relocated_input_limit (expr : Expr) (dimensions cells : Nat → Nat) :
    expressionInputLimit (relocateExpr dimensions cells expr) = 0 := by
  induction expr with
  | constant value => rfl
  | cell address => rfl
  | input address => rfl
  | binary operation left right ihLeft ihRight =>
    simp only [relocateExpr, expressionInputLimit, ihLeft, ihRight, Nat.max_self]

theorem point_room (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full))
    (offset : Nat) (ho : offset ≤ 512) :
    (state.register .address + BitVec.ofNat _ offset).toNat < allocated q full := by
  rw [base, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bank_offset_fits q full hq offset ho)]
  exact lt_of_le_of_lt (Nat.add_le_add_left ho _) (bank512_room q full)

theorem fixed_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (expr : Expr) (hc : expressionCellLimit expr ≤ 21)
    (hi : expressionInputLimit expr ≤ 3) (hs : expr.size ≤ 29)
    (state : WordState (bits q full)) (base : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    PackedAccessSafe (allocated q full) physical (fixedExprCode expr) state := by
  have below : (relocateExpr (dimensionBank 0) (variableBank 0) expr).Below 85 :=
    relocateExpr_below expr _ _ 85
      (by intro address ha; simp only [variableBank]; omega)
      (by intro address ha; simp only [dimensionBank, Nat.zero_add]; omega)
  have cells := cell_limit_of_below _ _ below
  apply compile_safe (relocateExpr (dimensionBank 0) (variableBank 0) expr) physical 128 (allocated q full) state
  · intro address ha
    exact point_room q full hq state base address (by omega)
  · intro address ha
    rw [relocated_input_limit] at ha
    omega
  · intro offset hlo hhi
    rw [relocateExpr_size] at hhi
    exact point_room q full hq state base offset (by omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
