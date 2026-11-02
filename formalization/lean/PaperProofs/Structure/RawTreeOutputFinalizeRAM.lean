module

public import PaperProofs.Structure.RawCandidateWorkspaceInit

/-! Actual final register writes. Earlier candidate and parent queries may
clobber value, so acceptance is restored by an executed instruction. The
node count and serialized length are read from already-written headers.
This block does not supply or assume the remaining output words. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawTreeOutputFinalizeRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def program : List PackingOp :=
  [.base (.base (.constant .address 5)),
   .base (.base (.loadHeap .old .address)),
   .base (.base (.constant .address 0)),
   .base (.base (.loadHeap .fresh .address)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.add .fresh .fresh .total)),
   .base (.base (.constant .address 2)),
   .base (.base (.loadHeap .total .address)),
   .base (.base (.add .fresh .fresh .total)),
   .base (.base (.constant .total 3)),
   .base (.base (.add .fresh .fresh .total)),
   .base (.base (.constant .value 1))]

theorem program_length : program.length = 13 := rfl

theorem program_noJump : ∀ op ∈ program, NoJump op := by simp [program, NoJump]

def paddingOp : PackingOp := .base (.base (.constant .value 0))

structure Finalized (start inputLength internalLength childrenLength nodes : Nat)
    (before after : NatState) : Prop where
  heap : after.heap = before.heap
  nodes : after.register .old = nodes
  length : after.register .fresh = 3 + inputLength + internalLength + childrenLength
  value : after.register .value = 1
  pc : after.pc = 5 * (start + 13)
  active : after.halted = false

private theorem runOps_effect (rom : PhysicalROM) (state : NatState) (start : Nat)
    (inputLength internalLength childrenLength nodes : Nat)
    (h0 : state.heap 0 = inputLength) (h1 : state.heap 1 = internalLength)
    (h2 : state.heap 2 = childrenLength) (h5 : state.heap 5 = nodes)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Finalized start inputLength internalLength childrenLength nodes state (runOps rom program state) := by
  constructor
  all_goals simp [program, runOps, natExecuteOp, Op.execute, Instruction.execute,
    h0, h1, h2, h5, hpc, hactive, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals omega

theorem finalize (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (hbound : start + 13 ≤ containing.length)
    (hcode : ∀ position < 13, containing.getD (start + position) paddingOp = program.getD position paddingOp)
    (state : NatState) (inputLength internalLength childrenLength nodes : Nat)
    (h0 : state.heap 0 = inputLength) (h1 : state.heap 1 = internalLength)
    (h2 : state.heap 2 = childrenLength) (h5 : state.heap 5 = nodes)
    (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Finalized start inputLength internalLength childrenLength nodes state (natRun rom containing 13 state) := by
  have hrun : natRun rom containing 13 state = runOps rom program state := by
    apply natRun_of_straight_segment rom containing program start
      (by change start + 13 ≤ containing.length; exact hbound) ?_ program_noJump state hpc hactive
    intro position hp
    have hh := hcode position (by simpa only [program_length] using hp)
    rw [List.getD_eq_getElem _ _ (by change position < 13 at hp; omega),
      List.getD_eq_getElem _ _ hp] at hh
    exact hh
  rw [hrun]
  exact runOps_effect rom state start inputLength internalLength childrenLength nodes h0 h1 h2 h5 hpc hactive

/-- In the final actual append layout, the following step fetches the
original HALT words. No uncharged host stop substitutes for that step. -/
theorem finalize_halt (rom : PhysicalROM) (left : List PackingOp) (state : NatState)
    (inputLength internalLength childrenLength nodes : Nat)
    (h0 : state.heap 0 = inputLength) (h1 : state.heap 1 = internalLength)
    (h2 : state.heap 2 = childrenLength) (h5 : state.heap 5 = nodes)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    let result := natRun rom (left ++ program) 14 state
    result.heap = state.heap ∧ result.register .old = nodes ∧
      result.register .fresh = 3 + inputLength + internalLength + childrenLength ∧
      result.register .value = 1 ∧ result.halted = true := by
  have hs := finalize rom (left ++ program) left.length
    (by simp only [List.length_append, program_length]; omega) ?_ state
    inputLength internalLength childrenLength nodes h0 h1 h2 h5 hpc hactive
  · have hp : (natRun rom (left ++ program) 13 state).pc = 5 * (left ++ program).length := by
      simpa only [List.length_append, program_length] using hs.pc
    have hh : natRun rom (left ++ program) 14 state =
        { natRun rom (left ++ program) 13 state with halted := true } := by
      rw [show 14 = 13 + 1 by decide, natRun_succ]
      exact natStep_halt rom (left ++ program) _ hp hs.active
    dsimp only
    rw [hh]
    exact ⟨hs.heap, hs.nodes, hs.length, hs.value, rfl⟩
  · intro position hp
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

end PaperProofs.Structure.LaminarTree.RawTreeOutputFinalizeRAM
