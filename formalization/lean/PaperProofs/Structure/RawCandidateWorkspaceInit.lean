module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.PackingWordBounds

/-! A fixed, active initialization block for the raw candidate workspace.
The two dimensions are read from the original input ROM.  Only heap cell 8
and the computed workspace header are written; no constructor is invoked. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceInit

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM

def candidateCount (N q : Nat) : Nat := N + q + 1

def workspaceBase (N q : Nat) : Nat := 8 * candidateCount N q * q + 16

/-- All dimensions and addresses are computed by this same sixteen-op body. -/
def program : List PackingOp :=
  [.base (.base (.constant .index 0)),
   .base (.base (.loadROM .input .old .index)),
   .base (.base (.constant .index 1)),
   .base (.base (.loadROM .input .fresh .index)),
   .base (.base (.add .total .old .fresh)),
   .base (.base (.constant .index 1)),
   .base (.base (.add .total .total .index)),
   .arithmetic .multiply .flag .total .fresh,
   .base (.base (.constant .index 8)),
   .arithmetic .multiply .flag .flag .index,
   .base (.base (.constant .index 16)),
   .base (.base (.add .flag .flag .index)),
   .base (.base (.constant .address 8)),
   .base (.base (.storeHeap .address .flag)),
   .base (.base (.minimum .address .flag .flag)),
   .base (.base (.storeHeap .address .total))]

theorem program_length : program.length = 16 := rfl

theorem program_noJump : ∀ op ∈ program, NoJump op := by
  simp [program, NoJump]

def paddingOp : PackingOp := .base (.base (.constant .value 0))

theorem candidateCount_pos (N q : Nat) : 0 < candidateCount N q := by
  unfold candidateCount
  omega

theorem workspaceBase_ge (N q : Nat) : 16 ≤ workspaceBase N q := by
  unfold workspaceBase
  omega

theorem candidateCount_fits (N q : Nat) :
    Fits (indexWidth 16 N q) (candidateCount N q) := by
  exact lt_of_le_of_lt (by unfold candidateCount; omega) (fits_checker_register_bound N q)

theorem workspaceBase_fits (N q : Nat) :
    Fits (indexWidth 16 N q) (workspaceBase N q) := by
  apply fits_indexWidth_of_lt_power
  have hbase : 2 ≤ N + q + 2 := by omega
  have hs : 4 ≤ (N + q + 2) ^ 2 := Nat.pow_le_pow_left hbase 2
  have hp : 16384 ≤ (N + q + 2) ^ 14 := Nat.pow_le_pow_left hbase 14
  have hproduct : candidateCount N q * q ≤ (N + q + 2) * (N + q + 2) :=
    Nat.mul_le_mul (by unfold candidateCount; omega) (by omega)
  calc
    workspaceBase N q ≤ 8 * ((N + q + 2) * (N + q + 2)) + 16 := by
      unfold workspaceBase
      nlinarith
    _ < (N + q + 2) ^ 2 * 16384 := by nlinarith
    _ ≤ (N + q + 2) ^ 2 * (N + q + 2) ^ 14 := Nat.mul_le_mul_left _ hp
    _ = (N + q + 2) ^ 16 := by rw [← pow_add]

/-- The complete visible handoff; every caller scratch cell is preserved
except the two cells whose values this block establishes. -/
structure Initialized (N q start : Nat) (before after : NatState) : Prop where
  base_cell : after.heap 8 = workspaceBase N q
  count_cell : after.heap (workspaceBase N q) = candidateCount N q
  heap_frame : ∀ address, address ≠ 8 → address ≠ workspaceBase N q →
    after.heap address = before.heap address
  value : after.register .value = before.register .value
  old : after.register .old = N
  fresh : after.register .fresh = q
  total : after.register .total = candidateCount N q
  flag : after.register .flag = workspaceBase N q
  address : after.register .address = workspaceBase N q
  index : after.register .index = 16
  pc : after.pc = 5 * (start + 16)
  active : after.halted = false

private theorem runOps_effect (q : Nat) (full : List (Finset (Fin q)))
    (start : Nat) (state : NatState) (hpc : state.pc = 5 * start)
    (hactive : state.halted = false) :
    Initialized full.length q start state (runOps (rawIncidenceROM q full) program state) := by
  constructor
  all_goals
    simp [program, runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute,
      raw_header_N, raw_header_q, candidateCount, workspaceBase, hpc, hactive,
      Nat.mul_comm, Nat.mul_assoc]
  · intro address h8 hbase
    simp [h8, hbase]
  · omega

/-- Execution is through the original encoded fetch/decode interpreter.
The slice premise only locates the fixed body in a larger caller program. -/
theorem initialize_workspace (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (start : Nat)
    (hbound : start + 16 ≤ containing.length)
    (hcode : ∀ position < 16, containing.getD (start + position) paddingOp =
      program.getD position paddingOp)
    (state : NatState) (hpc : state.pc = 5 * start) (hactive : state.halted = false) :
    Initialized full.length q start state
      (natRun (rawIncidenceROM q full) containing 16 state) := by
  have hrun : natRun (rawIncidenceROM q full) containing 16 state =
      runOps (rawIncidenceROM q full) program state := by
    apply natRun_of_straight_segment (rawIncidenceROM q full) containing program start
      (by change start + 16 ≤ containing.length; exact hbound) ?_
      program_noJump state hpc hactive
    intro position hp
    have hh := hcode position (by simpa only [program_length] using hp)
    rw [List.getD_eq_getElem _ _ (by change position < 16 at hp; omega),
      List.getD_eq_getElem _ _ hp] at hh
    exact hh
  rw [hrun]
  exact runOps_effect q full start state hpc hactive

theorem append_slice (left right : List PackingOp) :
    left.length + 16 ≤ (left ++ program ++ right).length ∧
      ∀ position < 16,
        (left ++ program ++ right).getD (left.length + position) paddingOp =
          program.getD position paddingOp := by
  constructor
  · simp only [List.length_append, program_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ program) right paddingOp _ (by
      simp only [List.length_append, program_length]; omega),
      List.getD_append_right left program paddingOp _ (by omega), Nat.add_sub_cancel_left]

/-- In an actual append layout the caller supplies no code-slice hypothesis. -/
theorem initialize_append (q : Nat) (full : List (Finset (Fin q)))
    (left right : List PackingOp) (state : NatState)
    (hpc : state.pc = 5 * left.length) (hactive : state.halted = false) :
    Initialized full.length q left.length state
      (natRun (rawIncidenceROM q full) (left ++ program ++ right) 16 state) := by
  exact initialize_workspace q full _ left.length (append_slice left right).1 (append_slice left right).2
    state hpc hactive

end PaperProofs.Structure.LaminarTree.RawCandidateWorkspaceInit
