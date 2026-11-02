module

public import Structure.PSTR_LeafUsedRun_028

/-! Real embedding of the leaf-used kernel in one containing program. The
assembler offset is a static code position, not a runtime dimension. Both
branches exit ACTIVE at the next containing instruction; no helper HALT or
PC reset is used. All containing code/index/finite-PC obligations are explicit. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafUsedEmbedded

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRLeafUsed

def leadAt (start : Nat) : List PackingOp :=
  [.base (.base (.loadHeap .value .address)),
   .base (.base (.constant .fresh (5 * (start + 36))))]

def kernel (start : Nat) : List PackingOp := leadAt start ++ [branch] ++ body

theorem leadAt_length (start : Nat) : (leadAt start).length = 2 := rfl
theorem kernel_length (start : Nat) : (kernel start).length = 36 := rfl

theorem leadAt_straight (start : Nat) : StraightProgram (leadAt start) := by
  simp [StraightProgram, StraightOp, leadAt]

theorem kernel_zero : kernel 0 = program := rfl

theorem kernel_lead (start i : Nat) (hi : i < (leadAt start).length) :
    (kernel start)[i]'(by rw [kernel_length]; rw [leadAt_length] at hi; omega) = (leadAt start)[i] := by
  change i < 2 at hi
  interval_cases i <;> rfl

theorem kernel_branch (start : Nat) : (kernel start)[2]'(by rw [kernel_length]; decide) = branch := rfl

theorem kernel_body (start i : Nat) (hi : i < body.length) :
    (kernel start)[3 + i]'(by rw [kernel_length]; rw [body_length] at hi; omega) = body[i] := by
  change ((leadAt start ++ [branch]) ++ body)[3 + i]'(by
    change 3 + i < 36
    have hh : i < 33 := hi
    omega) = body[i]
  rw [List.getElem_append_right (by change 3 ≤ 3 + i; omega)]
  simp only [show (leadAt start ++ [branch]).length = 3 from rfl, Nat.add_sub_cancel_left]

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (leadAt start ++ [branch]) state).heap = state.heap := rfl

theorem prefix_value {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (leadAt start ++ [branch]) state).register .value = state.heap (state.register .address) := rfl

theorem prefix_width {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (leadAt start ++ [branch]) state).register .total = state.register .total := rfl

theorem prefix_mask {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (leadAt start ++ [branch]) state).register .flag = state.register .flag := rfl

theorem prefix_pc {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) :
    (executeOps rom (leadAt start ++ [branch]) state).pc =
      if (state.heap (state.register .address)).toNat = 0 then BitVec.ofNat bits (5 * (start + 36))
      else BitVec.ofNat bits (5 * (start + 3)) := by
  have hpc : 5 * start + 5 + 5 + 5 = 5 * (start + 3) := by omega
  simp +decide only [leadAt, branch, executeOps, List.cons_append, List.nil_append,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hp, BitVec.ofNat_add_ofNat, hpc]

theorem prefix_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 3 state = executeOps rom (leadAt start ++ [branch]) state := by
  rw [show 3 = (leadAt start).length + 1 from rfl,
    PSTRWordSegments.segment_last rom whole (leadAt start) branch start
      (by rw [leadAt_length, kernel_length] at *; omega) ?_ ?_
      (leadAt_straight start) hwords hpcfit state hp ha, executeOps_append]
  · rfl
  · intro i hi
    exact (hcode i (by rw [kernel_length]; rw [leadAt_length] at hi; omega)).trans (kernel_lead start i hi)
  · simpa only [leadAt_length] using (hcode 2 (by rw [kernel_length]; decide)).trans (kernel_branch start)

theorem body_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * (start + 3))) (ha : state.halted = false) :
    packingRun rom whole 33 state = executeOps rom body state := by
  have hsize : start + 36 ≤ whole.length := by simpa only [kernel_length] using hbound
  have hbody (i : Nat) (hi : i < body.length) :
      whole[start + 3 + i]'(by rw [body_length] at hi; omega) = body[i] := by
    have hh := hcode (3 + i) (by rw [kernel_length]; rw [body_length] at hi; omega)
    simpa only [Nat.add_assoc] using hh.trans (kernel_body start i hi)
  simpa only [body_length] using PSTRWordSegments.straight_segment rom whole body (start + 3)
    (by rw [body_length]; omega) hbody body_straight hwords hpcfit state hp ha

theorem actual_none {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hz : (state.heap (state.register .address)).toNat = 0) :
    let after := packingRun rom whole 3 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 36)) ∧
      after.heap = state.heap ∧ after.register .value = BitVec.ofNat bits 0 := by
  have hv : state.heap (state.register .address) = BitVec.ofNat bits 0 := by
    have he := congrArg (BitVec.ofNat bits) hz
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  dsimp only
  rw [prefix_run rom whole start hbound hcode hwords hpcfit state hp ha]
  refine ⟨?_, ?_, prefix_heap rom start state, (prefix_value rom start state).trans hv⟩
  · rw [executeOps_halted, ha]
  · rw [prefix_pc rom start state hp, ite_eq_left hz]

theorem positive_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hz : ¬(state.heap (state.register .address)).toNat = 0) :
    packingRun rom whole 36 state = executeOps rom body (executeOps rom (leadAt start ++ [branch]) state) := by
  have hc : (executeOps rom (leadAt start ++ [branch]) state).pc =
      BitVec.ofNat bits (5 * (start + 3)) := by rw [prefix_pc rom start state hp, ite_eq_right hz]
  rw [show 36 = 3 + 33 from rfl, PSTRWordSegments.run_add,
    prefix_run rom whole start hbound hcode hwords hpcfit state hp ha]
  exact body_run rom whole start hbound hcode hwords hpcfit _ hc (by rw [executeOps_halted, ha])

theorem actual_some {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (start : Nat) (hbound : start + (kernel start).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (hz : ¬(state.heap (state.register .address)).toNat = 0) :
    let after := packingRun rom whole 36 state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (start + 36)) ∧ after.heap = state.heap := by
  dsimp only
  rw [positive_run rom whole start hbound hcode hwords hpcfit state hp ha hz]
  refine ⟨?_, ?_, (PSTRLeafUsedRun.body_heap rom _).trans (prefix_heap rom start state)⟩
  · rw [executeOps_halted, executeOps_halted, ha]
  · rw [executeOps_pc rom body _ body_straight, prefix_pc rom start state hp,
      ite_eq_right hz, body_length, BitVec.ofNat_add_ofNat]
    congr 1

end PaperProofs.Structure.LaminarTree.PSTRLeafUsedEmbedded
