module

public import Structure.PSTR_HD_HeadsOriginalInitial_079

/-! Uniform q=0/positive heads dispatcher without altering frozen111op tail.
It occupies8 fixed instructions before tailAt(queryEnd+8). q=0 actually jumps
to that SAME tail's stage probe, using address46; positive q actually falls
through to the original real endpoint locator. ONE query body remains atPC0. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

def dispatchLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .address 46)), .base (.base (.constant .total 1)),
   .base (.base (.loadROM .input .flag .total)), .base (.base (.constant .total (5 * (origin + 39))))]

def dispatchPadding : List PackingOp :=
  [.base (.base (.constant .total 0)), .base (.base (.constant .flag 0)), .base (.base (.constant .total 0))]

def uniformDispatch (origin : Nat) : List PackingOp := dispatchLead origin ++ [.jumpIfZero .flag .total] ++ dispatchPadding

def uniformHeadsProgram (queryBody : List PackingOp) : List PackingOp :=
  (queryBody ++ uniformDispatch queryBody.length) ++ tailAt (queryBody.length + 8)

theorem dispatchLead_length (origin : Nat) : (dispatchLead origin).length = 4 := rfl

theorem dispatchPadding_length : dispatchPadding.length = 3 := rfl

theorem uniformDispatch_length (origin : Nat) : (uniformDispatch origin).length = 8 := rfl

theorem uniformHeadsProgram_length (queryBody : List PackingOp) : (uniformHeadsProgram queryBody).length = queryBody.length + 119 := by
  simp only [uniformHeadsProgram, List.length_append, uniformDispatch_length, tailAt_length]

theorem dispatchLead_straight (origin : Nat) : StraightProgram (dispatchLead origin) := by
  simp [dispatchLead, StraightProgram, StraightOp]

theorem dispatchPadding_straight : StraightProgram dispatchPadding := by simp [dispatchPadding, StraightProgram, StraightOp]

theorem uniform_tail_code (queryBody : List PackingOp) :
    ∀ i (hi : i < (tailAt (queryBody.length + 8)).length),
      (uniformHeadsProgram queryBody)[(queryBody.length + 8) + i]'(by rw [uniformHeadsProgram_length]; rw [tailAt_length] at hi; omega) =
        (tailAt (queryBody.length + 8))[i] := by
  intro i hi
  change ((queryBody ++ uniformDispatch queryBody.length) ++ tailAt (queryBody.length + 8))[(queryBody.length + 8) + i]'(by
    simp only [List.length_append, uniformDispatch_length]; omega) = _
  rw [List.getElem_append_right (by rw [List.length_append, uniformDispatch_length]; omega)]
  simp only [List.length_append, uniformDispatch_length, Nat.add_sub_cancel_left]

theorem execute_dispatchLead {bits : Nat} (rom : PhysicalROM) (origin q : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hraw : (rom.words .input).getD 1 0 = q) :
    let after := executeOps rom (dispatchLead origin) state
    after.register .flag = BitVec.ofNat bits q ∧ after.register .total = BitVec.ofNat bits (5 * (origin + 39)) ∧
    after.register .address = BitVec.ofNat bits 46 ∧ after.halted = state.halted ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index := by
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  change (rom.words .input)[1]?.getD 0 = q at hraw
  simp +decide [dispatchLead, executeOps, packingExecuteOp, wordOp, wordInstruction, h1, hraw]

theorem containing_uniform_dispatch {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (origin q : Nat)
    (hbound : origin + (uniformDispatch origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (uniformDispatch origin).length), whole[origin + i]'(by omega) = (uniformDispatch origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hq : Fits bits q) (hraw : (rom.words .input).getD 1 0 = q) :
    ∃ steps ≤ 8,
    let after := packingRun rom whole steps state
    after.pc = (if q = 0 then BitVec.ofNat bits (5 * (origin + 39)) else BitVec.ofNat bits (5 * (origin + 8))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .value = state.register .value ∧
    after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
    after.register .index = state.register .index ∧ after.register .address = BitVec.ofNat bits 46 := by
  have lead_code : ∀ i (hi : i < (dispatchLead origin).length), whole[origin + i]'(by rw [uniformDispatch_length, dispatchLead_length] at *; omega) = (dispatchLead origin)[i] := by
    intro i hi
    have hc := hcode i (by rw [uniformDispatch_length, dispatchLead_length] at *; omega)
    change i < 4 at hi
    interval_cases i <;> exact hc
  have branch_code : whole[origin + (dispatchLead origin).length]'(by rw [uniformDispatch_length, dispatchLead_length] at *; omega) = .jumpIfZero .flag .total :=
    hcode 4 (by change 4 < 8; decide)
  have hlead := execute_dispatchLead rom origin q state hb hraw
  have h5 := fetched_conditional rom whole (dispatchLead origin) origin (origin + 39) q .flag
    (by rw [uniformDispatch_length] at hbound; rw [dispatchLead_length]; omega)
    lead_code branch_code (dispatchLead_straight origin) hwords hpcfit state hp ha hlead.1 hlead.2.1 hq
  rw [dispatchLead_length] at h5
  by_cases hz : q = 0
  · refine ⟨5, by omega, ?_⟩
    dsimp only
    rw [h5]
    exact ⟨by simp only [hz, ↓reduceIte], ha, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · let after5 := packingRun rom whole 5 state
    have pc5 : after5.pc = BitVec.ofNat bits (5 * (origin + 5)) := by dsimp only [after5]; rw [h5]; exact ite_eq_right hz
    have halt5 : after5.halted = false := by dsimp only [after5]; rw [h5]; exact ha
    have heap5 : after5.heap = state.heap := by dsimp only [after5]; rw [h5]; rfl
    have value5 : after5.register .value = state.register .value := by dsimp only [after5]; rw [h5]; rfl
    have old5 : after5.register .old = state.register .old := by dsimp only [after5]; rw [h5]; rfl
    have fresh5 : after5.register .fresh = state.register .fresh := by dsimp only [after5]; rw [h5]; rfl
    have index5 : after5.register .index = state.register .index := by dsimp only [after5]; rw [h5]; rfl
    have addr5 : after5.register .address = BitVec.ofNat bits 46 := by dsimp only [after5]; rw [h5]; rfl
    have padding_code : ∀ i (hi : i < dispatchPadding.length), whole[(origin + 5) + i]'(by rw [uniformDispatch_length, dispatchPadding_length] at *; omega) = dispatchPadding[i] := by
      intro i hi
      have hc := hcode (5 + i) (by rw [uniformDispatch_length, dispatchPadding_length] at *; omega)
      change i < 3 at hi
      interval_cases i <;> exact hc
    have run3 := straight_segment rom whole dispatchPadding (origin + 5)
      (by rw [uniformDispatch_length] at hbound; rw [dispatchPadding_length]; omega)
      padding_code dispatchPadding_straight hwords hpcfit after5 pc5 halt5
    rw [dispatchPadding_length] at run3
    refine ⟨8, le_refl _, ?_⟩
    dsimp only
    rw [show 8 = 5 + 3 from rfl, run_add, run3]
    refine ⟨?_, halt5, heap5, value5, old5, fresh5, index5, addr5⟩
    rw [ite_eq_right hz, executeOps_pc rom dispatchPadding after5 dispatchPadding_straight, pc5, BitVec.ofNat_add_ofNat]
    congr 1

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
