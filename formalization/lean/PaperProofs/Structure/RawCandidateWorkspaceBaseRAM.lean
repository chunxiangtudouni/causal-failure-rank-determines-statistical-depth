module

public import PaperProofs.Structure.RawCandidateWorkspaceInit

/-! Recover the workspace address from the original readonly dimensions,
without reading heap cell 8.  The output serializer overwrites that cell,
so the original mutable base-pointer slot cannot be reused there. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBaseRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

/-- Twelve actual instructions; old/fresh/value and the entire heap survive. -/
def program : List PackingOp :=
  [.base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .flag .index)),
   .base (.base (.add .total .total .flag)),
   .base (.base (.constant .index 1)),
   .base (.base (.add .total .total .index)),
   .arithmetic .multiply .address .total .flag,
   .base (.base (.constant .index 8)),
   .arithmetic .multiply .address .address .index,
   .base (.base (.constant .index 16)),
   .base (.base (.add .address .address .index))]

theorem program_length : program.length = 12 := rfl

theorem program_noJump : ∀ op ∈ program, NoJump op := by simp [program, NoJump]

def paddingOp : PackingOp := .base (.base (.constant .value 0))

structure Recovered (N q start : Nat) (before after : NatState) : Prop where
  heap : after.heap = before.heap
  old : after.register .old = before.register .old
  fresh : after.register .fresh = before.register .fresh
  value : after.register .value = before.register .value
  total : after.register .total = RawCandidateWorkspaceInit.candidateCount N q
  flag : after.register .flag = q
  address : after.register .address = RawCandidateWorkspaceInit.workspaceBase N q
  index : after.register .index = 16
  pc : after.pc = 5 * (start + 12)
  active : after.halted = false

private theorem runOps_effect (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Recovered full.length q start state (runOps (rawIncidenceROM q full) program state) := by
  constructor
  all_goals simp [program, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
    raw_header_N, raw_header_q, RawCandidateWorkspaceInit.candidateCount,
    RawCandidateWorkspaceInit.workspaceBase, hpc, hactive, Nat.mul_assoc, Nat.mul_comm]
  all_goals omega

/-- Every read is from raw ROM, not from the mutable serialized output. -/
theorem recover (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat) (hbound : start + 12 ≤ containing.length)
    (hcode : ∀ position < 12, containing.getD (start + position) paddingOp =
      program.getD position paddingOp)
    (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Recovered full.length q start state (natRun (rawIncidenceROM q full) containing 12 state) := by
  have hrun : natRun (rawIncidenceROM q full) containing 12 state =
      runOps (rawIncidenceROM q full) program state := by
    apply natRun_of_straight_segment (rawIncidenceROM q full) containing program start
      (by change start + 12 ≤ containing.length; exact hbound) ?_ program_noJump state hpc hactive
    intro position hp
    have hh := hcode position (by simpa only [program_length] using hp)
    rw [List.getD_eq_getElem _ _ (by change position < 12 at hp; omega),
      List.getD_eq_getElem _ _ hp] at hh
    exact hh
  rw [hrun]
  exact runOps_effect q full start state hpc hactive

theorem recover_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    Recovered full.length q left.length state
      (natRun (rawIncidenceROM q full) (left ++ program ++ right) 12 state) := by
  apply recover q full (left ++ program ++ right) left.length
    (by simp only [List.length_append, program_length]; omega) ?_ state hpc hactive
  intro position hp
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, program_length]; omega),
    List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceBaseRAM
