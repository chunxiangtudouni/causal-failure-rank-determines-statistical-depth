module

public import Structure.PSTR_BuildLower_FixedExprAccess_115
public import Structure.PSTR_BuildLower_RelativeValue_011

/-! Literal register arithmetic accesses only the seven real VM bank cells.
The local certificate concerns the actual Word prefixes, with the original
runtime base retained; no assumption about intermediate Nat values is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout
open RawTreePreprocessingClaims PA17PackedTranslator034 PA17UniformGenerator035b
section Generic
variable {bits : Nat}

theorem value_safe (op : ValueOp) (physical : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (room : ∀ reg : IndexedRAM.Register,
      (state.register .address + BitVec.ofNat bits (registerOffset reg)).toNat < heapWords) :
    PackedAccessSafe heapWords physical op.relativeLower state := by
  simp [BitVec.toNat_add] at room
  intro count hc
  have countBound : count < 13 := lt_of_lt_of_le hc (relativeValue_length op)
  interval_cases count <;> cases op <;>
    simp [ValueOp.relativeLower, relativeRead, relativeWrite, executeOps,
      packingExecuteOp, wordOp, wordInstruction, packingAccessFits, AccessFits] at hc ⊢
  all_goals exact room _

end Generic

theorem value_fixed_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (op : ValueOp) (physical : PhysicalROM) (state : WordState (bits q full))
    (base : state.register .address = BitVec.ofNat _ (controlBase q full)) :
    PackedAccessSafe (allocated q full) physical op.relativeLower state := by
  apply value_safe op physical (allocated q full) state
  intro reg
  exact point_room q full hq state base (registerOffset reg)
    (by have hh := registerSlot_bounds reg; change 32 ≤ registerOffset reg ∧ registerOffset reg < 39 at hh; omega)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.BankAccess
