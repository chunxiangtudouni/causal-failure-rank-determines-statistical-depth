module

public import Structure.PA17_A19QueryBridge_RuntimeTests_Control_015g

/-! Arbitrary-Word outside frames at every executed prefix of the budget
entry,tag/ancestor initialization and actual good/bad flag stores. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem budgetLead_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (address : BitVec bits)
    (h8 : address ≠ BitVec.ofNat bits (header + 8)) (h13 : address ≠ BitVec.ofNat bits (header + 13))
    (count : Nat) (hc : count ≤ 17) :
    (executeOps rom (budgetLead.take count) state).heap address = state.heap address := by
  interval_cases count <;>
    simp +decide [budgetLead, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, BitVec.ofNat_add_ofNat, Function.update_of_ne h8, Function.update_of_ne h13]

theorem tagTail_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (address : BitVec bits)
    (h10 : address ≠ BitVec.ofNat bits (header + 10)) (h9 : address ≠ BitVec.ofNat bits (header + 9))
    (count : Nat) (hc : count ≤ 11) :
    (executeOps rom (tagTail.take count) state).heap address = state.heap address := by
  interval_cases count <;>
    simp +decide [tagTail, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, BitVec.ofNat_add_ofNat, Function.update_of_ne h10, Function.update_of_ne h9]

theorem ancestorInit_prefix_frame {bits : Nat} (rom : PhysicalROM) (header : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header) (address : BitVec bits)
    (h11 : address ≠ BitVec.ofNat bits (header + 11)) (h14 : address ≠ BitVec.ofNat bits (header + 14))
    (h12 : address ≠ BitVec.ofNat bits (header + 12))
    (count : Nat) (hc : count ≤ 16) :
    (executeOps rom (ancestorInit.take count) state).heap address = state.heap address := by
  interval_cases count <;>
    simp +decide [ancestorInit, loadSlot, storeSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, BitVec.ofNat_add_ofNat, Function.update_of_ne h11, Function.update_of_ne h14, Function.update_of_ne h12]

theorem goodStore_prefix_frame {bits : Nat} (rom : PhysicalROM) (header budget : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 16 + budget))
    (count : Nat) (hc : count ≤ 10) :
    (executeOps rom (goodStore.take count) state).heap address = state.heap address := by
  interval_cases count <;>
    simp +decide [goodStore, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, hb, BitVec.ofNat_add_ofNat, Function.update_of_ne hne]

theorem budgetFinish_prefix_frame {bits : Nat} (rom : PhysicalROM) (header q budget : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 16 + (q + 2) + budget))
    (count : Nat) (hc : count ≤ 13) :
    (executeOps rom (budgetFinish.take count) state).heap address = state.heap address := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  interval_cases count <;>
    simp +decide [budgetFinish, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, hb, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, BitVec.ofNat_add_ofNat, Nat.add_comm]
  rw [show budget + (header + (q + 18)) = header + 16 + (q + 2) + budget by omega, Function.update_of_ne hne]

theorem actual_acceptFinish_prefix_frame {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header budget : Nat) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false)
    (address : BitVec bits) (hg : address ≠ BitVec.ofNat bits (header + 16 + budget))
    (h11 : address ≠ BitVec.ofNat bits (header + 11)) (h14 : address ≠ BitVec.ofNat bits (header + 14))
    (h12 : address ≠ BitVec.ofNat bits (header + 12)) (count : Nat) (hc : count ≤ 26) :
    (packingRun rom containing count state).heap address = state.heap address := by
  have hgood := execute_goodStore rom header budget state hh hb
  rw [actual_acceptFinish_prefix em rom state hp ha count hc]
  apply executeOps_prefix_frame_append rom goodStore ancestorInit state address
  · intro index hi
    exact goodStore_prefix_frame rom header budget state hh hb address hg index (by simpa only [goodStore_length] using hi)
  · intro index hi
    exact ancestorInit_prefix_frame rom header (executeOps rom goodStore state) hgood.2.2 address h11 h14 h12 index
      (by simpa only [ancestorInit_length] using hi)
  · change count ≤ acceptFinish.length
    rw [acceptFinish_length]
    exact hc

theorem actual_budgetFooter_prefix_frame {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header q budget : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hb : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 339))) (ha : state.halted = false)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (header + 16 + (q + 2) + budget))
    (count : Nat) (hc : count ≤ 16) :
    (packingRun rom containing count state).heap address = state.heap address := by
  rw [actual_footer_prefix em rom state hp ha count hc, budgetFooter_as_finish]
  apply executeOps_prefix_frame_append rom budgetFinish (back (5 * (origin + 7))) state address
  · intro index hi
    exact budgetFinish_prefix_frame rom header q budget state h1 hq hh hb address hne index
      (by simpa only [budgetFinish_length] using hi)
  · intro index _
    apply congrFun (executeOps_prefix_noStore _ _ _ ?_ index) address
    simp [back, backLead, HeapPreservingOp]
  · simpa only [← budgetFooter_as_finish, budgetFooter_length] using hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
