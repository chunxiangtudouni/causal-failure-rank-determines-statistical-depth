module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Control_015b

/-! Actual good-flag store followed by real ancestor initialization, and
actual bad-flag/footer data. These use only original heap cells. -/

@[expose] public section
set_option maxRecDepth 26000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem acceptFinish_result {bits : Nat} (rom : PhysicalROM) (header budget : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hgood : Fits bits (header + 16 + budget))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget) :
    let after := executeOps rom acceptFinish state
    let encoded := state.heap (BitVec.ofNat bits (header + 1))
    let flag := if encoded.toNat = 0 then BitVec.ofNat bits 0 else
      state.heap (BitVec.ofNat bits (header + 10))
    after.heap = Function.update
      (Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (header + 16 + budget))
            (state.heap (BitVec.ofNat bits (header + 10))))
          (BitVec.ofNat bits (header + 11)) encoded)
        (BitVec.ofNat bits (header + 14)) flag)
      (BitVec.ofNat bits (header + 12)) (state.heap (BitVec.ofNat bits 0)) ∧
      after.register .address = BitVec.ofNat bits header := by
  let good := executeOps rom goodStore state
  have hg := execute_goodStore rom header budget state hh hc
  have hi := execute_ancestorInit rom header good hroom hg.2.2
  have hne (physical : Nat) (hp : physical < header + 16 + budget) :
      BitVec.ofNat bits physical ≠ BitVec.ofNat bits (header + 16 + budget) := by
    intro heq
    have he := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (hp.trans hgood), Nat.mod_eq_of_lt hgood] at he
    omega
  have hnode : good.heap (BitVec.ofNat bits (header + 1)) = state.heap (BitVec.ofNat bits (header + 1)) := by
    rw [hg.1, Function.update_of_ne (hne _ (by omega))]
  have hzero : good.heap (BitVec.ofNat bits 0) = state.heap (BitVec.ofNat bits 0) := by
    rw [hg.1, Function.update_of_ne (hne _ (by omega))]
  dsimp only
  simpa only [acceptFinish, executeOps_append, good, hg.1, hg.2.1, hnode, hzero] using hi

theorem actual_acceptFinish_result {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header budget : Nat)
    (state : WordState bits) (hroom : Fits bits (header + 16))
    (hgood : Fits bits (header + 16 + budget))
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 196))) (ha : state.halted = false) :
    let after := packingRun rom containing 26 state
    let encoded := state.heap (BitVec.ofNat bits (header + 1))
    let flag := if encoded.toNat = 0 then BitVec.ofNat bits 0 else
      state.heap (BitVec.ofNat bits (header + 10))
    after.heap = Function.update
      (Function.update
        (Function.update
          (Function.update state.heap (BitVec.ofNat bits (header + 16 + budget))
            (state.heap (BitVec.ofNat bits (header + 10))))
          (BitVec.ofNat bits (header + 11)) encoded)
        (BitVec.ofNat bits (header + 14)) flag)
      (BitVec.ofNat bits (header + 12)) (state.heap (BitVec.ofNat bits 0)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 222)) ∧ after.halted = false := by
  have hc' := actual_acceptFinish_end em rom state hp ha
  have hd := acceptFinish_result rom header budget state hroom hgood hh hc
  exact ⟨by rw [hc'.1]; exact hd.1, by rw [hc'.1]; exact hd.2, hc'.2.1, hc'.2.2⟩

theorem actual_budgetFooter_result {bits origin : Nat} {containing : List PackingOp}
    (em : Embedded bits origin containing) (rom : PhysicalROM) (header q budget : Nat)
    (state : WordState bits) (h1 : Fits bits 1)
    (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hc : state.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits budget)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 339))) (ha : state.halted = false) :
    let after := packingRun rom containing 16 state
    after.heap = Function.update state.heap (BitVec.ofNat bits (header + 16 + (q + 2) + budget))
      (state.heap (BitVec.ofNat bits (header + 14))) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.pc = BitVec.ofNat bits (5 * (origin + 7)) ∧ after.halted = false := by
  have hc' := actual_budgetFooter_end em rom state hp ha
  have hd := execute_budgetFinish rom header q budget state h1 hq hh hc
  exact ⟨hc'.1.trans hd.1, hc'.2.1.trans hd.2, hc'.2.2.1, hc'.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
