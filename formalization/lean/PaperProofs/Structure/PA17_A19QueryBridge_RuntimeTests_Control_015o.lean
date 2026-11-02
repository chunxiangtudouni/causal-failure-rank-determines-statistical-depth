module
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015c

/-! Concrete acceptFinish slot producer for the actual budgetIndex body. -/
@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000
namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure AcceptFinishSlotsPost {bits : Nat} (headerBase budgetIndex encoded size entryBase origin : Nat)
    (goodBool : Bool) (before after : WordState bits) : Prop where
  heap : after.heap = Function.update
    (Function.update
      (Function.update
        (Function.update before.heap (BitVec.ofNat bits (headerBase + 16 + budgetIndex)) (BitVec.ofNat bits (bit goodBool)))
        (BitVec.ofNat bits (headerBase + 11)) (BitVec.ofNat bits encoded))
      (BitVec.ofNat bits (headerBase + 14)) (BitVec.ofNat bits (bit (goodBool && decide (encoded ≠ 0)))))
    (BitVec.ofNat bits (headerBase + 12)) (BitVec.ofNat bits size)
  header : after.register .address = BitVec.ofNat bits headerBase
  pc : after.pc = BitVec.ofNat bits (5 * (origin + 222))
  active : after.halted = false
  budget : after.heap (BitVec.ofNat bits (headerBase + 8)) = BitVec.ofNat bits budgetIndex
  node : after.heap (BitVec.ofNat bits (headerBase + 11)) = BitVec.ofNat bits encoded
  fuel : after.heap (BitVec.ofNat bits (headerBase + 12)) = BitVec.ofNat bits size
  row : after.heap (BitVec.ofNat bits (headerBase + 13)) = BitVec.ofNat bits entryBase
  flag : after.heap (BitVec.ofNat bits (headerBase + 14)) = BitVec.ofNat bits (bit (goodBool && decide (encoded ≠ 0)))
  good : after.heap (BitVec.ofNat bits (headerBase + 16 + budgetIndex)) = BitVec.ofNat bits (bit goodBool)
  «outside» : ∀ address, address ≠ BitVec.ofNat bits (headerBase + 16 + budgetIndex) →
    address ≠ BitVec.ofNat bits (headerBase + 11) → address ≠ BitVec.ofNat bits (headerBase + 12) →
    address ≠ BitVec.ofNat bits (headerBase + 14) → after.heap address = before.heap address

theorem actual_acceptFinish_slots {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM)
    (header budget encoded size entryBase : Nat) (goodBool : Bool) (state : WordState bits)
    (hroom : Fits bits (header + 16)) (hgood : Fits bits (header + 16 + budget)) (hencoded : Fits bits encoded)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (hn : state.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits encoded)
    (hg : state.heap (BitVec.ofNat bits (header + 10)) = BitVec.ofNat bits (bit goodBool))
    (he : state.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits entryBase)
    (hz : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size) :
    AcceptFinishSlotsPost header budget encoded size entryBase origin goodBool state
      (packingRun rom containing 26 state) := by
  let after := packingRun rom containing 26 state
  have hd := actual_acceptFinish_result em rom header budget state hroom hgood hh hc hp ha
  have hflag : (if encoded = 0 then BitVec.ofNat bits 0 else BitVec.ofNat bits (bit goodBool)) =
      BitVec.ofNat bits (bit (goodBool && decide (encoded ≠ 0))) := by
    by_cases hn0 : encoded = 0
    · simp [hn0, bit]
    · simp [hn0, bit]
  have hheap : after.heap = Function.update
      (Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (header + 16 + budget)) (BitVec.ofNat bits (bit goodBool)))
          (BitVec.ofNat bits (header + 11)) (BitVec.ofNat bits encoded))
        (BitVec.ofNat bits (header + 14)) (BitVec.ofNat bits (bit (goodBool && decide (encoded ≠ 0)))))
      (BitVec.ofNat bits (header + 12)) (BitVec.ofNat bits size) := by
    simpa only [hn, hg, hz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hencoded, hflag] using hd.1
  have hslotNe (left right : Nat) (hl : left ≤ 16) (hr : right ≤ 16) (hne : left ≠ right) :
      BitVec.ofNat bits (header + left) ≠ BitVec.ofNat bits (header + right) := by
    intro heq
    exact hne ((slots_eq_iff header left right hroom hl hr).mp heq)
  have hslotGood (offset : Nat) (ho : offset < 16) :
      BitVec.ofNat bits (header + offset) ≠ BitVec.ofNat bits (header + 16 + budget) := by
    intro heq
    have heq' := (ofNat_injective_of_fit (header + offset) (header + 16 + budget)
      ((show header + offset ≤ header + 16 by omega).trans_lt hroom) hgood).mp heq
    omega
  have hkeep (offset : Nat) (ho : offset < 16) (h11 : offset ≠ 11) (h12 : offset ≠ 12) (h14 : offset ≠ 14) :
      after.heap (BitVec.ofNat bits (header + offset)) = state.heap (BitVec.ofNat bits (header + offset)) := by
    rw [hheap, Function.update_of_ne (hslotNe offset 12 (by omega) (by decide) h12),
      Function.update_of_ne (hslotNe offset 14 (by omega) (by decide) h14),
      Function.update_of_ne (hslotNe offset 11 (by omega) (by decide) h11),
      Function.update_of_ne (hslotGood offset ho)]
  refine ⟨hheap, hd.2.1, hd.2.2.1, hd.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hkeep 8 (by decide) (by decide) (by decide) (by decide)).trans hc
  · rw [hheap, Function.update_of_ne (hslotNe 11 12 (by decide) (by decide) (by decide)),
      Function.update_of_ne (hslotNe 11 14 (by decide) (by decide) (by decide)), Function.update_self]
  · rw [hheap, Function.update_self]
  · exact (hkeep 13 (by decide) (by decide) (by decide) (by decide)).trans he
  · rw [hheap, Function.update_of_ne (hslotNe 14 12 (by decide) (by decide) (by decide)), Function.update_self]
  · rw [hheap, Function.update_of_ne (hslotGood 12 (by decide)).symm,
      Function.update_of_ne (hslotGood 14 (by decide)).symm,
      Function.update_of_ne (hslotGood 11 (by decide)).symm, Function.update_self]
  · intro address hgood' h11 h12 h14
    rw [hheap, Function.update_of_ne h12, Function.update_of_ne h14, Function.update_of_ne h11, Function.update_of_ne hgood']

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
