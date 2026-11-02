module

public import Structure.PSTR_BuildLower_CounterAccess_037
public import Structure.PSTR_BuildLower_ExprWord_025

/-! Direct Word primitive access for relative bank code and the real Expr
compiler. Addresses are justified by the actual bank base/finite offsets;
no whole-body NatRegistersFit or arithmetic-transport premise is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawTreePreprocessingClaims PA17PackedTranslator034
open PA17UniformGenerator035b
variable {bits : Nat}

theorem read_safe (physical : PhysicalROM) (offset heapWords : Nat) (target : IndexedRAM.Register) (state : WordState bits)
    (room : (state.register .address + BitVec.ofNat bits offset).toNat < heapWords) :
    PackedAccessSafe heapWords physical (relativeRead offset target) state := by
  simp [BitVec.toNat_add] at room
  intro count hc
  change count < 3 at hc
  interval_cases count <;>
    simp [relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits]
  exact room

theorem write_safe (physical : PhysicalROM) (offset heapWords : Nat) (state : WordState bits)
    (room : (state.register .address + BitVec.ofNat bits offset).toNat < heapWords) :
    PackedAccessSafe heapWords physical (relativeWrite offset) state := by
  simp [BitVec.toNat_add] at room
  intro count hc
  change count < 3 at hc
  interval_cases count <;>
    simp [relativeWrite, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits]
  exact room

theorem finish_safe (physical : PhysicalROM) (stack heapWords : Nat) (operation : Binary) (state : WordState bits)
    (room : (state.register .address + BitVec.ofNat bits stack).toNat < heapWords) :
    PackedAccessSafe heapWords physical (bankFinish stack operation) state := by
  change PackedAccessSafe heapWords physical (relativeRead stack .old ++ [operation.instruction]) state
  apply PackedAccessSafe.append heapWords physical _ _ state (read_safe physical stack heapWords .old state room)
  intro count hc
  change count < 1 at hc
  have he : count = 0 := by omega
  subst count
  cases operation <;> trivial

private theorem size_positive (expr : Expr) : 0 < expr.size := by
  cases expr <;> simp only [Expr.size] <;> omega

theorem compile_safe (expr : Expr) (physical : PhysicalROM) (stack heapWords : Nat) (state : WordState bits)
    (cells : ∀ address < expressionCellLimit expr,
      (state.register .address + BitVec.ofNat bits address).toNat < heapWords)
    (inputs : ∀ address < expressionInputLimit expr, address < (physical.words .input).length)
    (room : ∀ offset, stack ≤ offset → offset < stack + expr.size →
      (state.register .address + BitVec.ofNat bits offset).toNat < heapWords) :
    PackedAccessSafe heapWords physical (bankCompile stack expr) state := by
  revert cells inputs room
  induction expr generalizing stack state with
  | constant value =>
    intro cells inputs room count hc
    change count < 1 at hc
    have he : count = 0 := by omega
    subst count
    trivial
  | cell address =>
    intro cells inputs room
    exact read_safe physical address heapWords .value state (cells address (by change address < address + 1; omega))
  | input address =>
    intro cells inputs room count hc
    change count < 2 at hc
    have haddress := inputs address (by change address < address + 1; omega)
    have hmod : (BitVec.ofNat bits address).toNat < (physical.words .input).length :=
      (Nat.mod_le address (2 ^ bits)).trans_lt haddress
    interval_cases count <;>
      simp [bankCompile, executeOps, packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits]
    exact hmod
  | binary operation left right ihLeft ihRight =>
    intro cells inputs room
    let first := executeOps physical (bankCompile stack left) state
    let middle := executeOps physical (relativeWrite stack) first
    let last := executeOps physical (bankCompile (stack + 1) right) middle
    have firstBase : first.register .address = state.register .address := by
      simpa only [List.take_length] using (bankCompile_word_frame left physical stack).1 state (bankCompile stack left).length
    have middleBase : middle.register .address = state.register .address := by
      change first.register .address = state.register .address
      exact firstBase
    have lastBase : last.register .address = state.register .address := by
      have hh := (bankCompile_word_frame right physical (stack + 1)).1 middle (bankCompile (stack + 1) right).length
      rw [List.take_length] at hh
      exact hh.trans middleBase
    change PackedAccessSafe heapWords physical
      (bankCompile stack left ++ (relativeWrite stack ++ (bankCompile (stack + 1) right ++ bankFinish stack operation))) state
    apply PackedAccessSafe.append heapWords physical _ _ state
    · apply ihLeft
      · intro address ha
        exact cells address (by change address < max (expressionCellLimit left) (expressionCellLimit right); omega)
      · intro address ha
        exact inputs address (by change address < max (expressionInputLimit left) (expressionInputLimit right); omega)
      · intro offset hlo hhi
        exact room offset hlo (by simp only [Expr.size]; omega)
    · apply PackedAccessSafe.append heapWords physical _ _ first
      · apply write_safe
        rw [firstBase]
        exact room stack le_rfl (by have hh := size_positive (.binary operation left right); omega)
      · apply PackedAccessSafe.append heapWords physical _ _ middle
        · apply ihRight
          · intro address ha
            rw [middleBase]
            exact cells address (by change address < max (expressionCellLimit left) (expressionCellLimit right); omega)
          · intro address ha
            exact inputs address (by change address < max (expressionInputLimit left) (expressionInputLimit right); omega)
          · intro offset hlo hhi
            rw [middleBase]
            exact room offset (by omega) (by simp only [Expr.size]; omega)
        · apply finish_safe
          rw [lastBase]
          exact room stack le_rfl (by have hh := size_positive (.binary operation left right); omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
