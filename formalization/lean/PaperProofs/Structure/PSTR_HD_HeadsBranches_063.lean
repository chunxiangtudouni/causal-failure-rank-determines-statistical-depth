module

public import PaperProofs.Structure.PSTR_HD_HeadsSerialized_062

/-! The heads tests are fetched from the SAME whole encoded instruction
array. The branch theorem operates on the real Word conditional instruction;
its numeric test is an internal register fact established by059, not an opcode. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem fetched_conditional {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (start target test : Nat) (condition : Register)
    (hbound : start + lead.length + 1 ≤ whole.length)
    (hcode : ∀ i (hi : i < lead.length), whole[start + i]'(by omega) = lead[i])
    (hlast : whole[start + lead.length]'(by omega) = .jumpIfZero condition .total)
    (hstraight : StraightProgram lead) (hwords : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hcond : (executeOps rom lead state).register condition = BitVec.ofNat bits test)
    (htarget : (executeOps rom lead state).register .total = BitVec.ofNat bits (5 * target))
    (htest : Fits bits test) :
    packingRun rom whole (lead.length + 1) state =
      {executeOps rom lead state with pc :=
        (if test = 0 then BitVec.ofNat bits (5 * target) else BitVec.ofNat bits (5 * (start + lead.length + 1)))} := by
  rw [segment_last rom whole lead (.jumpIfZero condition .total) start hbound hcode hlast hstraight hwords hpcfit state hp ha]
  have htn : (BitVec.ofNat bits test).toNat = test := Nat.mod_eq_of_lt htest
  have hsum : 5 * start + 5 * lead.length + 5 = 5 * (start + lead.length + 1) := by omega
  by_cases hz : test = 0 <;>
    simp [packingExecuteOp, hcond, htarget, htn, executeOps_pc rom lead state hstraight,
      hp, BitVec.ofNat_add_ofNat, hsum, hz]

theorem fetched_conditional_active {bits : Nat} (rom : PhysicalROM) (whole lead : List PackingOp)
    (start : Nat) (condition : Register)
    (hbound : start + lead.length + 1 ≤ whole.length)
    (hcode : ∀ i (hi : i < lead.length), whole[start + i]'(by omega) = lead[i])
    (hlast : whole[start + lead.length]'(by omega) = .jumpIfZero condition .total)
    (hstraight : StraightProgram lead) (hwords : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    let after := packingRun rom whole (lead.length + 1) state
    after.halted = false ∧ after.heap = (executeOps rom lead state).heap ∧
      after.register = (executeOps rom lead state).register := by
  rw [segment_last rom whole lead (.jumpIfZero condition .total) start hbound hcode hlast hstraight hwords hpcfit state hp ha]
  exact ⟨(executeOps_halted rom lead state).trans ha, rfl, rfl⟩

theorem firstReturn_fetched {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (origin current : Nat)
    (hbound : origin + 40 ≤ whole.length)
    (hconst : whole[origin + 38]'(by omega) = .base (.base (.constant .total (5 * (origin + 80)))))
    (hbranch : whole[origin + 39]'(by omega) = .jumpIfZero .old .total)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (origin + 38))) (ha : state.halted = false)
    (hs : state.register .old = BitVec.ofNat bits current) (hf : Fits bits current) :
    packingRun rom whole 2 state =
      {executeOps rom [.base (.base (.constant .total (5 * (origin + 80))))] state with pc :=
        (if current = 0 then BitVec.ofNat bits (5 * (origin + 80)) else BitVec.ofNat bits (5 * (origin + 40)))} := by
  have h := fetched_conditional rom whole [.base (.base (.constant .total (5 * (origin + 80))))]
    (origin + 38) (origin + 80) current .old (by change origin + 38 + 1 + 1 ≤ whole.length; omega) ?_ ?_
    (by simp [StraightProgram, StraightOp]) hwords hpcfit state hp ha
    (by simpa +decide [executeOps, packingExecuteOp, wordOp, wordInstruction] using hs)
    rfl hf
  · exact h
  · intro i hi
    change i < 1 at hi
    have he : i = 0 := by omega
    subst i
    exact hconst
  · exact hbranch

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
