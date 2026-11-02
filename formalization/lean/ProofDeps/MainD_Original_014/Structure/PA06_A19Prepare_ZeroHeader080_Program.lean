module

public import Structure.PA06_A19Prepare_RuntimeHeader019

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED fixed zero-tool handler body. The existing runtime45-op
prelude reads only the original ROM N/q headers and computes the width.
The following15 real instructions copy that result to header3 and clear
headers0/1/2 plus live stage/failed4/5. No incoming heap answer is needed.
The body returns active and leaves the containing global HALT to its owner. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  CompactControllerClaims PA17UniformGenerator035a PA17UniformGenerator035i

def finish : List PackingOp :=
  [.base (.base (.constant .index 2)), .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .address 3)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .value 0)),
   .base (.base (.constant .address 0)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 1)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 2)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 4)), .base (.base (.storeHeap .address .value)),
   .base (.base (.constant .address 5)), .base (.base (.storeHeap .address .value))]

def programAt (start : Nat) : List PackingOp := dimensionPrelude start ++ finish

def clock (N : Nat) : Nat := dimensionClock N 0 + 15

def NatHeader (N : Nat) (heap : Nat → Nat) : Prop :=
  heap 0 = 0 ∧ heap 1 = 0 ∧ heap 2 = 0 ∧ heap 3 = indexWidth 32 N 0 ∧ heap 4 = 0 ∧ heap 5 = 0

theorem finish_length : finish.length = 15 := rfl

theorem programAt_length (start : Nat) : (programAt start).length = 60 := by
  simp only [programAt, List.length_append, dimensionPrelude_length, finish_length]

theorem clock_eq (N : Nat) : clock N = 6 * Nat.clog 2 (N + 2) + 52 := by
  simp only [clock, dimensionClock, Nat.add_zero, Nat.clog_one_right, Nat.mul_zero, Nat.zero_add]

theorem clock_le (N : Nat) : clock N ≤ 6 * N + 58 := by
  have bound := dimensionClock_le N 0
  simp only [Nat.mul_zero, Nat.add_zero] at bound
  unfold clock
  omega

theorem finish_noJump : ∀ op ∈ finish, NoJump op := by simp [finish, NoJump]

theorem finish_heap (rom : PhysicalROM) (state : NatState) :
    (runOps rom finish state).heap =
      Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update state.heap 3 (state.heap 2)) 0 0) 1 0) 2 0) 4 0) 5 0 := rfl

theorem finish_header (rom : PhysicalROM) (N : Nat) (state : NatState)
    (hwidth : state.heap 2 = indexWidth 32 N 0) :
    NatHeader N (runOps rom finish state).heap := by
  simp [NatHeader, finish_heap, hwidth]

theorem program_run (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (left right : List PackingOp) (before : NatState)
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false) :
    let code := left ++ programAt left.length ++ right
    let after := natRun (controllerInput 0 full used) code (clock full.length) before
    after.pc = 5 * (left.length + 60) ∧ after.halted = false ∧ NatHeader full.length after.heap := by
  let rom := controllerInput 0 full used
  let code := left ++ programAt left.length ++ right
  let lead := left ++ dimensionPrelude left.length
  let middle := natRun rom code (dimensionClock full.length 0) before
  have pre : middle.pc = 5 * (left.length + 45) ∧ middle.halted = false ∧
      middle.heap 2 = indexWidth 32 full.length 0 := by
    have actual := PA06A19PrepareRuntimeHeader019.prelude_run 0 full used left (finish ++ right) before hpc ha
    simpa only [middle, code, rom, programAt, List.append_assoc] using
      (And.intro actual.1 (And.intro actual.2.1 actual.2.2.2.1))
  have leadLength : lead.length = left.length + 45 := by
    simp only [lead, List.length_append, dimensionPrelude_length]
  have finishRun : natRun rom code 15 middle = runOps rom finish middle := by
    have actual := natRun_of_straight_segment rom (lead ++ finish ++ right) finish lead.length
      (by simp only [List.length_append]; omega) (segment_index lead finish right)
      finish_noJump middle (by rw [leadLength]; exact pre.1) pre.2.1
    simpa only [code, programAt, lead, List.append_assoc, finish_length] using actual
  have run : natRun rom code (clock full.length) before = runOps rom finish middle := by
    change natRun rom code (dimensionClock full.length 0 + 15) before = _
    rw [natRun_add]
    exact finishRun
  dsimp only
  rw [run]
  refine ⟨?_, (runOps_halted rom finish middle).trans pre.2.1, finish_header rom full.length middle pre.2.2⟩
  rw [runOps_pc rom finish middle finish_noJump, finish_length, pre.1]
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080
