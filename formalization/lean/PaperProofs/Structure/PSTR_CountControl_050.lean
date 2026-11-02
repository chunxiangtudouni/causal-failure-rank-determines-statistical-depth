module

public import PaperProofs.Structure.PSTR_HD_WordSegments_014

/-! Actual outer-loop control, independent of runtime dimensions. The test
reads t from physical header0 and compares it with the ordinary node register.
Only static containing-code jump positions are parameters of these blocks. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountControl

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

def testLead (exit : Nat) : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadHeap .total .address)),
   .base (.subtract .flag .total .index),
   .base (.base (.constant .address (5 * exit)))]

def testBlock (exit : Nat) : List PackingOp := testLead exit ++ [.jumpIfZero .flag .address]

def backLead (target : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)),
   .base (.base (.constant .address (5 * target)))]

def backBlock (target : Nat) : List PackingOp := backLead target ++ [.jumpIfZero .flag .address]

theorem testLead_length (exit : Nat) : (testLead exit).length = 4 := rfl
theorem testBlock_length (exit : Nat) : (testBlock exit).length = 5 := rfl
theorem backLead_length (target : Nat) : (backLead target).length = 2 := rfl
theorem backBlock_length (target : Nat) : (backBlock target).length = 3 := rfl

theorem testLead_straight (exit : Nat) : StraightProgram (testLead exit) := by
  simp [testLead, StraightProgram, StraightOp]

theorem backLead_straight (target : Nat) : StraightProgram (backLead target) := by
  simp [backLead, StraightProgram, StraightOp]

theorem test_pc {bits : Nat} (rom : PhysicalROM) (start exit size node : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hi : state.register .index = BitVec.ofNat bits node)
    (hsize : Fits bits size) (hnode : Fits bits node) :
    (executeOps rom (testBlock exit) state).pc =
      if size - node = 0 then BitVec.ofNat bits (5 * exit)
      else BitVec.ofNat bits (5 * (start + 5)) := by
  have hd : Fits bits (size - node) := (Nat.sub_le _ _).trans_lt hsize
  have hpc : 5 * start + 5 + 5 + 5 + 5 + 5 = 5 * (start + 5) := by omega
  simp +decide only [testBlock, testLead, List.cons_append, List.nil_append, executeOps,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hp, ht, hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsize,
    Nat.mod_eq_of_lt hnode, Nat.mod_eq_of_lt hd, BitVec.ofNat_add_ofNat, hpc]

theorem test_pc_of_lt {bits : Nat} (rom : PhysicalROM) (start exit size node : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hi : state.register .index = BitVec.ofNat bits node)
    (hsize : Fits bits size) (hlt : node < size) :
    (executeOps rom (testBlock exit) state).pc = BitVec.ofNat bits (5 * (start + 5)) := by
  rw [test_pc rom start exit size node state hp ht hi hsize (hlt.trans hsize), ite_eq_right (by omega)]

theorem test_pc_at_end {bits : Nat} (rom : PhysicalROM) (start exit size : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start))
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hi : state.register .index = BitVec.ofNat bits size) (hsize : Fits bits size) :
    (executeOps rom (testBlock exit) state).pc = BitVec.ofNat bits (5 * exit) := by
  rw [test_pc rom start exit size size state hp ht hi hsize hsize, Nat.sub_self, ite_eq_left rfl]

theorem test_payload {bits : Nat} (rom : PhysicalROM) (exit : Nat) (state : WordState bits) :
    let after := executeOps rom (testBlock exit) state
    after.heap = state.heap ∧ after.register .index = state.register .index ∧
      after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
      after.register .value = state.register .value := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem test_prefix_heap {bits : Nat} (rom : PhysicalROM) (exit : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 5) :
    (executeOps rom ((testBlock exit).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem back_pc {bits : Nat} (rom : PhysicalROM) (target : Nat) (state : WordState bits) :
    (executeOps rom (backBlock target) state).pc = BitVec.ofNat bits (5 * target) := by
  simp +decide only [backBlock, backLead, List.cons_append, List.nil_append, executeOps,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    BitVec.toNat_ofNat, Nat.zero_mod]

theorem back_payload {bits : Nat} (rom : PhysicalROM) (target : Nat) (state : WordState bits) :
    let after := executeOps rom (backBlock target) state
    after.heap = state.heap ∧ after.register .index = state.register .index ∧
      after.register .old = state.register .old ∧ after.register .fresh = state.register .fresh ∧
      after.register .value = state.register .value := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem back_prefix_heap {bits : Nat} (rom : PhysicalROM) (target : Nat) (state : WordState bits)
    (count : Nat) (hc : count ≤ 3) :
    (executeOps rom ((backBlock target).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem fetched_test {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start exit : Nat)
    (hbound : start + (testBlock exit).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (testBlock exit).length), whole[start + i]'(by omega) = (testBlock exit)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 5 state = executeOps rom (testBlock exit) state := by
  rw [testBlock, executeOps_append]
  apply PSTRWordSegments.segment_last rom whole (testLead exit) (.jumpIfZero .flag .address) start
    (by rw [testBlock_length, testLead_length] at *; omega) ?_ ?_
    (testLead_straight exit) hw hpcfit state hp ha
  · intro i hi
    exact (hcode i (by rw [testBlock_length]; rw [testLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (hcode (testLead exit).length (by rw [testBlock_length, testLead_length]; decide)).trans
      (List.getElem_append_right' (testLead exit) (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

theorem fetched_back {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target : Nat)
    (hbound : start + (backBlock target).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (backBlock target).length), whole[start + i]'(by omega) = (backBlock target)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 3 state = executeOps rom (backBlock target) state := by
  rw [backBlock, executeOps_append]
  apply PSTRWordSegments.segment_last rom whole (backLead target) (.jumpIfZero .flag .address) start
    (by rw [backBlock_length, backLead_length] at *; omega) ?_ ?_
    (backLead_straight target) hw hpcfit state hp ha
  · intro i hi
    exact (hcode i (by rw [backBlock_length]; rw [backLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (hcode (backLead target).length (by rw [backBlock_length, backLead_length]; decide)).trans
      (List.getElem_append_right' (backLead target) (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

theorem test_trace {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 5 state).length ≤ 60 := packingDynamicTrace_length_le rom whole 5 state

theorem back_trace {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 3 state).length ≤ 36 := packingDynamicTrace_length_le rom whole 3 state

end PaperProofs.Structure.LaminarTree.PSTRCountControl
