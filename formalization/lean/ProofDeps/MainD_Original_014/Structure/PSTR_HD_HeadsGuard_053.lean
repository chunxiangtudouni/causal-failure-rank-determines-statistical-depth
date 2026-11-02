module

public import Structure.PSTR_HD_HeadsEndpoint_051
public import Common.PSTR_HD_HeadScan_052

/-! A real five-op successor-rank comparison. Two saturating subtractions
and a real Word addition implement equality without a free comparison opcode. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

def gap (left right : Nat) : Nat := (left - right) + (right - left)

theorem gap_zero_iff (left right : Nat) : gap left right = 0 ↔ left = right := by
  unfold gap
  omega

theorem gap_le_max (left right : Nat) : gap left right ≤ max left right := by
  by_cases h : left ≤ right
  · rw [max_eq_right h]
    unfold gap
    omega
  · rw [max_eq_left (by omega)]
    unfold gap
    omega

theorem gap_fits {bits : Nat} (left right : Nat) (hl : Fits bits left) (hr : Fits bits right) :
    Fits bits (gap left right) :=
  (gap_le_max left right).trans_lt (max_lt_iff.mpr ⟨hl, hr⟩)

def successorGuard : List PackingOp :=
  [.base (.base (.constant .total 1)),
   .base (.base (.add .fresh .fresh .total)),
   .base (.subtract .flag .fresh .value),
   .base (.subtract .value .value .fresh),
   .base (.base (.add .flag .flag .value))]

theorem successorGuard_length : successorGuard.length = 5 := rfl

theorem successorGuard_straight : StraightProgram successorGuard := by
  simp [successorGuard, StraightProgram, StraightOp]

theorem execute_successorGuard {bits : Nat} (rom : PhysicalROM) (rank bad : Nat) (state : WordState bits)
    (hrank : Fits bits rank) (hbad : Fits bits (bad + 1))
    (hv : state.register .value = BitVec.ofNat bits rank) (hb : state.register .fresh = BitVec.ofNat bits bad) :
    let after := executeOps rom successorGuard state
    after.register .flag = BitVec.ofNat bits (gap (bad + 1) rank) ∧
      after.register .old = state.register .old ∧ after.register .index = state.register .index ∧
      after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted := by
  have hrn : (BitVec.ofNat bits rank).toNat = rank := Nat.mod_eq_of_lt hrank
  have hbn : (BitVec.ofNat bits (bad + 1)).toNat = bad + 1 := Nat.mod_eq_of_lt hbad
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  simp +decide only [successorGuard, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hv, hb, BitVec.ofNat_add_ofNat, hrn, hbn, gap]

theorem successorGuard_zero_iff {bits : Nat} (rom : PhysicalROM) (rank bad : Nat) (state : WordState bits)
    (hrank : Fits bits rank) (hbad : Fits bits (bad + 1))
    (hv : state.register .value = BitVec.ofNat bits rank) (hb : state.register .fresh = BitVec.ofNat bits bad) :
    ((executeOps rom successorGuard state).register .flag).toNat = 0 ↔ bad + 1 = rank := by
  rw [(execute_successorGuard rom rank bad state hrank hbad hv hb).1, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (gap_fits (bad + 1) rank hbad hrank)]
  exact gap_zero_iff (bad + 1) rank

theorem successorGuard_prefix_access {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (state : WordState bits)
    (count : Nat) (hc : count < successorGuard.length) :
    packingAccessFits rom heapWords (executeOps rom (successorGuard.take count) state) successorGuard[count] := by
  change count < 5 at hc
  interval_cases count <;> simp [successorGuard, packingAccessFits, AccessFits]

theorem containing_successorGuard {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + successorGuard.length ≤ whole.length)
    (hcode : ∀ i (hi : i < successorGuard.length), whole[start + i]'(by omega) = successorGuard[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 5 state = executeOps rom successorGuard state :=
  straight_segment rom whole successorGuard start hbound hcode successorGuard_straight hwords hpcfit state hp ha

theorem successorGuard_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 5 state).length ≤ 60 := packingDynamicTrace_length_le rom whole 5 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
