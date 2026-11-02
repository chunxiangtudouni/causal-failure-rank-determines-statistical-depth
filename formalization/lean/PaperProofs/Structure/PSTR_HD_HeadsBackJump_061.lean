module

public import PaperProofs.Structure.PSTR_HD_HeadsTests_059

/-! Real code-fetched unconditional edges for the heads loop. In particular,
target0 jumps to the SAME literal query body with the SAME heap/registers;
there is no CPU reset, host callback, separate program, or intermediate HALT. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

def jumpLead (target : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 0)), .base (.base (.constant .total (5 * target)))]

theorem jumpBack_split (target : Nat) : jumpBack target = jumpLead target ++ [.jumpIfZero .flag .total] := rfl

theorem jumpLead_length (target : Nat) : (jumpLead target).length = 2 := rfl

theorem jumpLead_straight (target : Nat) : StraightProgram (jumpLead target) := by
  simp [jumpLead, StraightProgram, StraightOp]

theorem execute_jumpBack {bits : Nat} (rom : PhysicalROM) (target : Nat) (state : WordState bits) :
    let after := packingExecuteOp rom (.jumpIfZero .flag .total) (executeOps rom (jumpLead target) state)
    after.pc = BitVec.ofNat bits (5 * target) ∧ after.halted = state.halted ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address ∧
    after.register .flag = BitVec.ofNat bits 0 ∧ after.register .total = BitVec.ofNat bits (5 * target) := by
  simp +decide [jumpLead, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem containing_jumpBack {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target : Nat)
    (hbound : start + (jumpBack target).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (jumpBack target).length), whole[start + i]'(by omega) = (jumpBack target)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 3 state =
      packingExecuteOp rom (.jumpIfZero .flag .total) (executeOps rom (jumpLead target) state) := by
  apply segment_last rom whole (jumpLead target) (.jumpIfZero .flag .total) start
    (by rw [jumpBack_length] at hbound; rw [jumpLead_length]; omega) ?_ ?_
    (jumpLead_straight target) hwords hpcfit state hp ha
  · intro i hi
    have hc := hcode i (by rw [jumpBack_length, jumpLead_length] at *; omega)
    have hg : (jumpBack target)[i]'(by rw [jumpBack_length, jumpLead_length] at *; omega) = (jumpLead target)[i] := by
      change (jumpLead target ++ [.jumpIfZero .flag .total])[i]'(by simp only [List.length_append, List.length_cons, List.length_nil]; omega) = _
      exact List.getElem_append_left hi
    exact hc.trans hg
  · have hc := hcode 2 (by rw [jumpBack_length]; decide)
    exact hc

theorem same_heap_query_jump {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hbound : start + (jumpBack 0).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (jumpBack 0).length), whole[start + i]'(by omega) = (jumpBack 0)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    let after := packingRun rom whole 3 state
    after.pc = BitVec.ofNat bits 0 ∧ after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = state.register .address := by
  rw [containing_jumpBack rom whole start 0 hbound hcode hwords hpcfit state hp ha]
  have h := execute_jumpBack rom 0 state
  exact ⟨h.1, h.2.1.trans ha, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

theorem jumpBack_prefix_access {bits : Nat} (rom : PhysicalROM) (target heapWords : Nat)
    (state : WordState bits) (count : Nat) (hc : count < (jumpBack target).length) :
    packingAccessFits rom heapWords (executeOps rom ((jumpBack target).take count) state) (jumpBack target)[count] := by
  change count < 3 at hc
  interval_cases count <;> trivial

theorem jumpBack_prefix_heap {bits : Nat} (rom : PhysicalROM) (target : Nat)
    (state : WordState bits) (count : Nat) (hc : count ≤ (jumpBack target).length) :
    (executeOps rom ((jumpBack target).take count) state).heap = state.heap := by
  change count ≤ 3 at hc
  interval_cases count <;> rfl

theorem jumpBack_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 3 state).length ≤ 36 := packingDynamicTrace_length_le rom whole 3 state

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
