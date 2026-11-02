module

public import Structure.PSTR_BuildLower_ViewStep_045
public import Structure.PSTR_BuildLower_DynamicStep_043

/-! The finite original source view only observes the actual low packed and
ordinary physical words. Writes to the disjoint runtime control bank therefore
preserve it, including every actual expression/control prefix. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ViewFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
variable {bits : Nat}

theorem congr_below (q C0 C indexBase I : Nat) (left right : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hC : C0 ≤ C) (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (heq : ∀ point < indexBase + I, left (BitVec.ofNat bits point) = right (BitVec.ofNat bits point))
    (a : Nat) (ha : a < C0 + I) :
    PA06A19PreparePackedView013.view q C0 C indexBase left a =
      PA06A19PreparePackedView013.view q C0 C indexBase right a := by
  by_cases hc : a < C0
  · rw [PA06A19PreparePackedView013.view_capacity_scalar q C0 C indexBase left hC a hc,
      PA06A19PreparePackedView013.view_capacity_scalar q C0 C indexBase right hC a hc]
    apply congrArg CapacityBits.decodeScalar
    apply congrArg List.ofFn
    funext position
    have hm := Nat.mul_le_mul_right (CapacityBits.width q) (show a + 1 ≤ C by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    have hoff : a * CapacityBits.width q + position.val < C * CapacityBits.width q := by
      have hp := position.isLt
      omega
    have hd : (a * CapacityBits.width q + position.val) / bits < packedCapacityWords q C bits :=
      (Nat.div_lt_iff_lt_mul hb).mpr (hoff.trans_le (packedCapacityWords_mul_bits q C hb))
    dsimp only
    rw [PA06A19PreparePackedView013.dataHeap_word, PA06A19PreparePackedView013.dataHeap_word,
      heq _ (by omega)]
  · rw [PA06A19PreparePackedView013.view_index q C0 C indexBase left a (by omega),
      PA06A19PreparePackedView013.view_index q C0 C indexBase right a (by omega), heq _ (by omega)]

theorem bankRange_below (rom : PhysicalROM) (code : List PackingOp) (lo hi : Nat)
    (hf : BankRangeFrame (bits := bits) rom code lo hi) (hlo : lo ≤ hi)
    (state : WordState bits) (base point : Nat) (hbase : state.register .address = BitVec.ofNat bits base)
    (hend : Fits bits (base + hi)) (hp : point < base + lo) (count : Nat) :
    (executeOps rom (code.take count) state).heap (BitVec.ofNat bits point) = state.heap (BitVec.ofNat bits point) := by
  apply hf.2
  intro offset hol hoh
  rw [hbase, BitVec.ofNat_add_ofNat]
  apply word_address_ne
  · exact lt_of_lt_of_le hp (Nat.add_le_add_left hlo base) |>.trans hend
  · exact lt_trans (by omega : base + offset < base + hi) hend
  · omega

theorem bankRange_view (rom : PhysicalROM) (code : List PackingOp) (lo hi : Nat)
    (hf : BankRangeFrame (bits := bits) rom code lo hi) (hlo : lo ≤ hi)
    (q C0 C indexBase I base : Nat) (state : WordState bits)
    (hstate : state.register .address = BitVec.ofNat bits base) (hend : Fits bits (base + hi))
    (hb : 0 < bits) (hC : C0 ≤ C) (hpacked : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hdisjoint : indexBase + I ≤ base + lo) (count a : Nat) (ha : a < C0 + I) :
    PA06A19PreparePackedView013.view q C0 C indexBase (executeOps rom (code.take count) state).heap a =
      PA06A19PreparePackedView013.view q C0 C indexBase state.heap a := by
  apply congr_below q C0 C indexBase I _ _ hb hC hpacked ?_ a ha
  intro point hp
  exact bankRange_below rom code lo hi hf hlo state base point hstate hend (hp.trans_le hdisjoint) count

theorem relativeWrite_range (rom : PhysicalROM) (offset lo hi : Nat) (hl : lo ≤ offset) (hh : offset < hi) :
    BankRangeFrame (bits := bits) rom (relativeWrite offset) lo hi := by
  refine ⟨fun state count => relativeWrite_prefix_base rom offset state count, ?_⟩
  intro state point outside count
  exact relativeWrite_prefix_frame rom offset state point (outside offset hl hh) count

theorem dynamic_range (rom : PhysicalROM) (target : Register) (expr : PA17UniformGenerator035b.Expr) :
    BankRangeFrame (bits := bits) rom (DynamicStep.code target expr) 32 (max 39 (128 + expr.size)) := by
  apply bankRangeFrame_append
  · apply bankRangeFrame_mono rom _ 128 (128 + expr.size) 32 (max 39 (128 + expr.size)) (by decide)
      (Nat.le_max_right _ _)
    simpa only [fixedExprCode, relocateExpr_size] using
      bankCompile_word_frame (relocateExpr (dimensionBank 0) (variableBank 0) expr) rom 128
  · exact relativeWrite_range rom (registerOffset target) _ _
      (registerSlot_bounds target).1 ((registerSlot_bounds target).2.trans_le (Nat.le_max_left _ _))

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ViewFrame
