module

public import PaperProofs.Structure.PSTR_HD_HeadsWriteSafe_073

/-! The three actual decisions of the fixed heads controller: terminal,
finite initial rank, and successor rank equality. All tests are real Word
register/heap operations fetched from the SAME literal whole program. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem terminal_continue {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin stage N : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 40))) (ha : state.halted = false)
    (hs : stage < N) (hN : Fits bits N)
    (hindex : state.register .index = BitVec.ofNat bits N) (hold : state.register .old = BitVec.ofNat bits stage) :
    let after := packingRun rom whole 3 state
    after.pc = BitVec.ofNat bits (5 * (origin + 43)) ∧ after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address := by
  dsimp only
  have htest := execute_terminalLead rom origin stage N state hN (hs.trans hN) hindex hold
  have hrun := fetched_conditional rom whole (terminalLead origin) (origin + 40) (origin + 104) (N - stage) .flag
    (by have h := tailAt_length origin; rw [terminalLead_length]; omega)
    (terminalLead_tail_code whole origin hbound hcode) (hcode 42 (by change 42 < 111; decide))
    (terminalLead_straight origin) hwords hpcfit state hp ha htest.1 htest.2.1 ((Nat.sub_le N stage).trans_lt hN)
  rw [terminalLead_length] at hrun
  rw [hrun]
  refine ⟨?_, ha, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ite_eq_right (by omega)

theorem finite_decision {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint q rank : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 43))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hslot : state.heap (BitVec.ofNat bits (endpoint + 3)) = BitVec.ofNat bits (q + 2 - rank))
    (hr : rank ≤ q + 2) (hq : Fits bits (q + 2)) :
    let after := packingRun rom whole 5 state
    after.pc = (if rank = q + 2 then BitVec.ofNat bits (5 * (origin + 56)) else BitVec.ofNat bits (5 * (origin + 48))) ∧
    after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address := by
  dsimp only
  have htest := execute_finiteLead rom origin endpoint (q + 2 - rank) state haddr hslot
  have hrun := fetched_conditional rom whole (finiteLead origin) (origin + 43) (origin + 56) (q + 2 - rank) .flag
    (by have h := tailAt_length origin; rw [finiteLead_length]; omega)
    (finiteLead_tail_code whole origin hbound hcode) (hcode 47 (by change 47 < 111; decide))
    (finiteLead_straight origin) hwords hpcfit state hp ha htest.1 htest.2.1 ((Nat.sub_le _ _).trans_lt hq)
  rw [finiteLead_length] at hrun
  rw [hrun]
  refine ⟨?_, ha, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases hz : rank = q + 2
  · simp only [hz, Nat.sub_self, ↓reduceIte]
  · rw [ite_eq_right (by omega), ite_eq_right hz]

theorem guard_decision {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (origin endpoint rank bad : Nat)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 48))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits endpoint)
    (hslot : state.heap (BitVec.ofNat bits endpoint) = BitVec.ofNat bits rank)
    (hbad : state.register .fresh = BitVec.ofNat bits bad) (hr : Fits bits rank) (hb : Fits bits (bad + 1)) :
    let after := packingRun rom whole 8 state
    after.pc = (if bad + 1 = rank then BitVec.ofNat bits (5 * (origin + 67)) else BitVec.ofNat bits (5 * (origin + 56))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .old = state.register .old ∧
    after.register .index = state.register .index ∧ after.register .address = state.register .address := by
  dsimp only
  have htest := execute_guardLead rom origin endpoint rank bad state haddr hslot hbad hr hb
  have hrun := fetched_conditional rom whole (guardLead origin) (origin + 48) (origin + 67) (gap (bad + 1) rank) .flag
    (by have h := tailAt_length origin; rw [guardLead_length]; omega)
    (guardLead_tail_code whole origin hbound hcode) (hcode 55 (by change 55 < 111; decide))
    (guardLead_straight origin) hwords hpcfit state hp ha htest.1 htest.2.1 (gap_fits _ _ hb hr)
  rw [guardLead_length] at hrun
  rw [hrun]
  refine ⟨?_, ha, rfl, rfl, rfl, rfl⟩
  simp only [gap_zero_iff]

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
