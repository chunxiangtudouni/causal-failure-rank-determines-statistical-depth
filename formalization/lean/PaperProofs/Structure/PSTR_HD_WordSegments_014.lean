module

public import PaperProofs.Structure.PackingExecutionCost

/-! Actual Word-level straight segments inside an encoded containing program.
Data arithmetic may use the original BitVec truncation semantics; only PC/
code/access obligations appropriate to that literal program are assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWordSegments

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

theorem run_add (rom : PhysicalROM) (program : List PackingOp) (left right : Nat)
    (state : WordState bits) :
    packingRun rom program (left + right) state =
      packingRun rom program right (packingRun rom program left state) := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, packingRun]
  | succ left ih =>
    rw [Nat.succ_add]
    change packingRun rom program (left + right)
      (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state) = _
    exact ih _

theorem straight_segment (rom : PhysicalROM) (program block : List PackingOp)
    (start : Nat) (hbound : start + block.length ≤ program.length)
    (hcode : ∀ i (hi : i < block.length), program[start + i]'(by omega) = block[i])
    (hstraight : StraightProgram block) (hwords : WordsFit bits (packingCode program))
    (hpcfit : Fits bits (5 * program.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * start))
    (ha : state.halted = false) :
    packingRun rom program block.length state = executeOps rom block state := by
  induction block generalizing start state with
  | nil => rfl
  | cons op later ih =>
    have hindex : start < program.length := by simp only [List.length_cons] at hbound; omega
    have hhead := hcode 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hhead
    change packingRun rom program later.length
      (packingStep rom ((packingCode program).map (BitVec.ofNat bits)) state) =
        executeOps rom later (packingExecuteOp rom op state)
    have hpcNat : state.pc.toNat = 5 * start := by
      rw [hpc, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 hindex.le) hpcfit)
    rw [packingStep_of_index rom program state start hindex hwords hpcNat ha, hhead]
    apply ih (start + 1) (by simp only [List.length_cons] at hbound; omega) ?_ ?_
      (packingExecuteOp rom op state) ?_ ?_
    · intro i hi
      have hh := hcode (i + 1) (by simpa using hi)
      change program[start + (i + 1)]'(by simp only [List.length_cons] at hbound; omega) = later[i] at hh
      convert hh using 1
      congr 1
      omega
    · intro other ho
      exact hstraight other (List.mem_cons_of_mem _ ho)
    · rw [packingExecuteOp_pc rom op state (hstraight op List.mem_cons_self), hpc, BitVec.ofNat_add_ofNat]
      congr 1
    · rw [packingExecuteOp_halted, ha]

theorem segment_last (rom : PhysicalROM) (program lead : List PackingOp) (last : PackingOp)
    (start : Nat) (hbound : start + lead.length + 1 ≤ program.length)
    (hcode : ∀ i (hi : i < lead.length), program[start + i]'(by omega) = lead[i])
    (hlast : program[start + lead.length]'(by omega) = last)
    (hstraight : StraightProgram lead) (hwords : WordsFit bits (packingCode program))
    (hpcfit : Fits bits (5 * program.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * start))
    (ha : state.halted = false) :
    packingRun rom program (lead.length + 1) state =
      packingExecuteOp rom last (executeOps rom lead state) := by
  rw [packingRun_succ, straight_segment rom program lead start (by omega) hcode hstraight hwords hpcfit state hpc ha]
  have hp : (executeOps rom lead state).pc.toNat = 5 * (start + lead.length) := by
    rw [executeOps_pc rom lead state hstraight, hpc, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
    have hnum : 5 * start + 5 * lead.length = 5 * (start + lead.length) := by omega
    rw [hnum]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 (by omega)) hpcfit)
  rw [packingStep_of_index rom program _ (start + lead.length) (by omega) hwords hp
    (by rw [executeOps_halted, ha]), hlast]

theorem segment_prefix (rom : PhysicalROM) (program lead : List PackingOp) (last : PackingOp)
    (start : Nat) (hbound : start + lead.length + 1 ≤ program.length)
    (hcode : ∀ i (hi : i < lead.length), program[start + i]'(by omega) = lead[i])
    (hlast : program[start + lead.length]'(by omega) = last)
    (hstraight : StraightProgram lead) (hwords : WordsFit bits (packingCode program))
    (hpcfit : Fits bits (5 * program.length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * start))
    (ha : state.halted = false) (count : Nat) (hc : count ≤ lead.length + 1) :
    packingRun rom program count state = executeOps rom ((lead ++ [last]).take count) state := by
  by_cases hb : count ≤ lead.length
  · rw [List.take_append_of_le_length hb]
    have hl : (lead.take count).length = count := List.length_take_of_le hb
    conv_lhs => rw [← hl]
    apply straight_segment rom program (lead.take count) start (by omega) ?_ ?_ hwords hpcfit state hpc ha
    · intro i hi
      have hi' : i < lead.length := by rw [hl] at hi; omega
      simpa only [List.getElem_take] using hcode i hi'
    · intro op ho
      exact hstraight op (List.mem_of_mem_take ho)
  · have he : count = lead.length + 1 := by omega
    rw [he, segment_last rom program lead last start hbound hcode hlast hstraight hwords hpcfit state hpc ha,
      List.take_of_length_le (by simp), executeOps_append]
    rfl

end PaperProofs.Structure.LaminarTree.PSTRWordSegments
