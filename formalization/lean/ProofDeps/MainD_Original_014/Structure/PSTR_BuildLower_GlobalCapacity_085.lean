module

public import Structure.PSTR_BuildLower_PreparedLayout_054
public import Structure.PSTR_BuildLower_SourceRep_048
public import Structure.PSTR_BuildLower_ControlDataFrame_061
public import Structure.PSTR_BuildLower_CopyData_078

/-! The whole NEW packed capacity is an additional internal invariant, not
a consequence of the smaller original C0 simulation view. Actual clear029
produces it. True physical frames transport it through VM/counter/Expr bank
writes, without imposing a new qualification on the original caller. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.GlobalCapacity
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

def Bounded (q : Nat) (full : List (Finset (Fin q))) (heap : BitVec (bits q full) → BitVec (bits q full)) : Prop :=
  CapacityPrefixBounded q (capacity q full) (CompactControllerClaims.logicalHeap q (capacity q full) heap)

theorem of_packed_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (before after : BitVec (bits q full) → BitVec (bits q full)) (bounded : Bounded q full before)
    (frame : ∀ point < indexBase q full, after (BitVec.ofNat _ point) = before (BitVec.ofNat _ point)) :
    Bounded q full after := by
  unfold Bounded at bounded ⊢
  simp only [CompactControllerClaims.logicalHeap, ite_eq_right (Nat.ne_of_gt hq)] at bounded ⊢
  intro address ha
  have hh := ViewFrame.congr_below q (capacity q full) (capacity q full) (indexBase q full) 0 after before
    (by have hb := bits_room q full; omega) le_rfl le_rfl
    (by intro point hp; exact frame point (by simpa only [Nat.add_zero] using hp)) address (by omega)
  rw [PA06A19PreparePackedView013.view_capacity _ _ _ _ _ address ha,
    PA06A19PreparePackedView013.view_capacity _ _ _ _ _ address ha] at hh
  exact hh.trans_le (bounded address ha)

theorem bank_range_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (block : List PackingOp) (lo hi : Nat) (horder : lo ≤ hi) (hhi : hi ≤ 512)
    (frame : BankRangeFrame (bits := bits q full) physical block lo hi) (state : WordState (bits q full))
    (hbase : state.register .address = BitVec.ofNat _ (controlBase q full)) (bounded : Bounded q full state.heap)
    (count : Nat) : Bounded q full (executeOps physical (block.take count) state).heap := by
  apply of_packed_frame q full hq state.heap _ bounded
  intro point hp
  apply ViewFrame.bankRange_below physical block lo hi frame horder state (controlBase q full) point hbase
    (bank_offset_fits q full hq hi hhi) ?_ count
  have hr := ordinary_before_control q full
  omega

theorem bank_actual_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (block : List PackingOp) (lo hi : Nat) (horder : lo ≤ hi) (hhi : hi ≤ 512)
    (frame : BankRangeFrame (bits := bits q full) physical block lo hi) (straight : StraightProgram block)
    (state : WordState (bits q full)) (hbase : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : Bounded q full state.heap) (left right : List PackingOp)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ block ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ block ++ right).length))
    (count : Nat) (hc : count ≤ block.length) :
    Bounded q full (packingRun physical (left ++ block ++ right) count state).heap := by
  rw [SourceRep.straight_prefix physical left block right state straight hcode hpcfit hpc ha count hc]
  exact bank_range_prefix q full hq physical block lo hi horder hhi frame state hbase bounded count

theorem value_actual_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (op : ValueOp) (state : WordState (bits q full))
    (hbase : state.register .address = BitVec.ofNat _ (controlBase q full)) (bounded : Bounded q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ op.relativeLower ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ op.relativeLower ++ right).length))
    (count : Nat) (hc : count ≤ op.relativeLower.length) :
    Bounded q full (packingRun physical (left ++ op.relativeLower ++ right) count state).heap :=
  bank_actual_prefix q full hq physical op.relativeLower 32 39 (by decide) (by decide)
    (SourceRep.value_range op physical) (relativeValue_straight op) state hbase bounded left right hpc ha hcode hpcfit count hc

theorem dynamic_actual_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (target : Register) (expr : PA17UniformGenerator035b.Expr) (hs : expr.size ≤ 29)
    (state : WordState (bits q full))
    (hbase : state.register .address = BitVec.ofNat _ (controlBase q full)) (bounded : Bounded q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ DynamicStep.code target expr ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ DynamicStep.code target expr ++ right).length))
    (count : Nat) (hc : count ≤ (DynamicStep.code target expr).length) :
    Bounded q full (packingRun physical (left ++ DynamicStep.code target expr ++ right) count state).heap :=
  bank_actual_prefix q full hq physical (DynamicStep.code target expr) 32 (max 39 (128 + expr.size))
    (by have hh := Nat.le_max_left 39 (128 + expr.size); omega) (by omega)
    (ViewFrame.dynamic_range physical target expr) (DynamicStep.code_straight target expr)
    state hbase bounded left right hpc ha hcode hpcfit count hc

theorem copy_actual_prefix (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (source target : Nat) (ht : target < 512) (state : WordState (bits q full))
    (hbase : state.register .address = BitVec.ofNat _ (controlBase q full)) (bounded : Bounded q full state.heap)
    (left right : List PackingOp) (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ relativeCopy source target ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ relativeCopy source target ++ right).length))
    (count : Nat) (hc : count ≤ 6) :
    Bounded q full (packingRun physical (left ++ relativeCopy source target ++ right) count state).heap :=
  bank_actual_prefix q full hq physical (relativeCopy source target) target (target + 1) (by omega) (by omega)
    (ControlDataFrame.copy_range physical source target) (SourceRep.copy_straight source target)
    state hbase bounded left right hpc ha hcode hpcfit count (by simpa only [relativeCopy_length] using hc)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.GlobalCapacity
