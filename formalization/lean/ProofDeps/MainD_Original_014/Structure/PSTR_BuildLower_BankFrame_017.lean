module

public import Structure.PSTR_BuildLower_BankExpr_009

/-! Direct Word all-prefix frame for the runtime-bank Expr compiler. This proof
does not use a Nat no-overflow transport or a backend performance premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035b

variable {bits : Nat}

def BankRangeFrame (rom : PhysicalROM) (code : List PackingOp) (lo hi : Nat) : Prop :=
  (∀ (state : WordState bits) count,
    (executeOps rom (code.take count) state).register .address = state.register .address) ∧
  ∀ (state : WordState bits) (point : BitVec bits),
    (∀ offset, lo ≤ offset → offset < hi →
      point ≠ state.register .address + BitVec.ofNat bits offset) → ∀ count,
    (executeOps rom (code.take count) state).heap point = state.heap point

theorem bankRangeFrame_mono (rom : PhysicalROM) (code : List PackingOp) (lo hi outerLo outerHi : Nat)
    (hlo : outerLo ≤ lo) (hhi : hi ≤ outerHi) (hf : BankRangeFrame (bits := bits) rom code lo hi) :
    BankRangeFrame (bits := bits) rom code outerLo outerHi := by
  refine ⟨hf.1, ?_⟩
  intro state point outside count
  exact hf.2 state point (fun offset ha hb => outside offset (hlo.trans ha) (hb.trans_le hhi)) count

theorem bankRangeFrame_append (rom : PhysicalROM) (left right : List PackingOp) (lo hi : Nat)
    (hl : BankRangeFrame (bits := bits) rom left lo hi)
    (hr : BankRangeFrame (bits := bits) rom right lo hi) :
    BankRangeFrame (bits := bits) rom (left ++ right) lo hi := by
  constructor
  · intro state count
    rw [List.take_append, executeOps_append, hr.1, hl.1]
  · intro state point outside count
    let after := executeOps rom (left.take count) state
    have hb : after.register .address = state.register .address := hl.1 state count
    have hleft := hl.2 state point outside count
    have hright := hr.2 after point (by
      intro offset ha hc
      rw [hb]
      exact outside offset ha hc) (count - left.length)
    rw [List.take_append, executeOps_append]
    exact hright.trans hleft

private theorem range_read (rom : PhysicalROM) (offset lo hi : Nat) :
    BankRangeFrame (bits := bits) rom (relativeRead offset .value) lo hi := by
  refine ⟨fun state count => relativeRead_prefix_base rom offset .value state (by decide) count, ?_⟩
  intro state point _ count
  exact relativeRead_prefix_heap rom offset .value point state count

private theorem range_write (rom : PhysicalROM) (offset lo hi : Nat) (hlo : lo ≤ offset) (hhi : offset < hi) :
    BankRangeFrame (bits := bits) rom (relativeWrite offset) lo hi := by
  refine ⟨fun state count => relativeWrite_prefix_base rom offset state count, ?_⟩
  intro state point outside count
  exact relativeWrite_prefix_frame rom offset state point (outside offset hlo hhi) count

private theorem range_finish (rom : PhysicalROM) (stack lo hi : Nat) (operation : Binary) :
    BankRangeFrame (bits := bits) rom (bankFinish stack operation) lo hi := by
  constructor
  · intro state count
    by_cases hc : count ≤ 4
    · interval_cases count <;> cases operation <;>
        simp [bankFinish, Binary.instruction, executeOps, packingExecuteOp, wordOp, wordInstruction]
    · rw [List.take_of_length_le (by change 4 ≤ count; omega)]
      cases operation <;> rfl
  · intro state point _ count
    by_cases hc : count ≤ 4
    · interval_cases count <;> cases operation <;>
        simp [bankFinish, Binary.instruction, executeOps, packingExecuteOp, wordOp, wordInstruction]
    · rw [List.take_of_length_le (by change 4 ≤ count; omega)]
      cases operation <;> rfl

theorem bankCompile_word_frame (expr : Expr) (rom : PhysicalROM) (stack : Nat) :
    BankRangeFrame (bits := bits) rom (bankCompile stack expr) stack (stack + expr.size) := by
  induction expr generalizing stack with
  | constant value =>
    constructor
    · intro state count
      cases count <;> simp [bankCompile, executeOps, packingExecuteOp, wordOp, wordInstruction]
    · intro state point _ count
      cases count <;> simp [bankCompile, executeOps, packingExecuteOp, wordOp, wordInstruction]
  | cell address => exact range_read rom address _ _
  | input address =>
    constructor
    · intro state count
      cases count with
      | zero => rfl
      | succ count => cases count <;>
          simp [bankCompile, executeOps, packingExecuteOp, wordOp, wordInstruction]
    · intro state point _ count
      cases count with
      | zero => rfl
      | succ count => cases count <;>
          simp [bankCompile, executeOps, packingExecuteOp, wordOp, wordInstruction]
  | binary operation left right ihl ihr =>
    simp only [bankCompile]
    apply bankRangeFrame_append
    · exact bankRangeFrame_mono rom _ _ _ _ _ le_rfl (by simp only [Expr.size]; omega) (ihl stack)
    · apply bankRangeFrame_append
      · exact range_write rom stack _ _ le_rfl (by simp only [Expr.size]; omega)
      · apply bankRangeFrame_append
        · exact bankRangeFrame_mono rom _ _ _ _ _ (by omega) (by simp only [Expr.size]; omega) (ihr (stack + 1))
        · exact range_finish rom stack _ _ operation

theorem bankCompile_word_base_prefix (expr : Expr) (rom : PhysicalROM) (stack : Nat)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((bankCompile stack expr).take count) state).register .address = state.register .address :=
  (bankCompile_word_frame expr rom stack).1 state count

theorem bankCompile_word_nat_frame (expr : Expr) (rom : PhysicalROM) (stack base point : Nat)
    (state : WordState bits) (hbase : state.register .address = BitVec.ofNat bits base)
    (hpoint : Fits bits point) (hend : Fits bits (base + stack + expr.size))
    (outside : point < base + stack ∨ base + stack + expr.size ≤ point) (count : Nat) :
    (executeOps rom ((bankCompile stack expr).take count) state).heap (BitVec.ofNat bits point) =
      state.heap (BitVec.ofNat bits point) := by
  apply (bankCompile_word_frame expr rom stack).2
  intro offset hlo hhi
  rw [hbase, BitVec.ofNat_add_ofNat]
  apply word_address_ne hpoint
  · apply lt_trans (show base + offset < base + stack + expr.size by omega) hend
  · rcases outside with ha | ha <;> omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
