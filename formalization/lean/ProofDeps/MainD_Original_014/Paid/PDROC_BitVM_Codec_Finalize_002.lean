module

public import Paid.PDROC_BitVM_Codec_Finalize_001
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Codec.Finalize

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native

def callerSize (contents : Stack → List Bool) : ℕ := RatMarshal.globalSize contents

/-- Untouched arbitrary caller data must still be paid in ALL-state
space. The computational growth term uses only the four actual operated
stacks, including old physical workspace and the real emission ticks. -/
def spaceBudget (contents : Stack → List Bool) : ℕ :=
  callerSize contents + PDROC.BitVM.Common.sourcePushCap program Finset.univ * timeBudget contents

def callerTimeCoefficient : ℕ := 64 * OutputList.listTimeCoefficient
def callerSpaceCoefficient : ℕ :=
  PDROC.BitVM.Common.sourcePushCap program Finset.univ * callerTimeCoefficient + 1

theorem inputSize_le (contents : Stack → List Bool) : inputSize contents ≤ 4 * callerSize contents := by
  have a := RatMarshal.initial_le_globalSize contents 0
  have b := RatMarshal.initial_le_globalSize contents 22
  have c := RatMarshal.initial_le_globalSize contents 23
  have d := RatMarshal.initial_le_globalSize contents 24
  dsimp only [inputSize, callerSize]
  omega

/-- A coarse all32-stack cubic is available without requiring any bound
on old ROM/register/heap/temporary words beyond their actual input size. -/
theorem timeBudget_callerCubic (contents : Stack → List Bool) :
    timeBudget contents ≤ callerTimeCoefficient * (callerSize contents + 1)^3 := by
  have size := inputSize_le contents
  have powers : (inputSize contents + 1)^3 ≤ (4 * (callerSize contents + 1))^3 :=
    Nat.pow_le_pow_left (by omega) 3
  calc
    timeBudget contents ≤ OutputList.listTimeCoefficient * (4 * (callerSize contents + 1))^3 :=
      Nat.mul_le_mul_left _ powers
    _ = callerTimeCoefficient * (callerSize contents + 1)^3 := by unfold callerTimeCoefficient; ring

theorem spaceBudget_callerCubic (contents : Stack → List Bool) :
    spaceBudget contents ≤ callerSpaceCoefficient * (callerSize contents + 1)^3 := by
  let U := callerSize contents + 1
  have positive : 1 ≤ U := by dsimp only [U]; omega
  have square : U ≤ U^2 := by
    simpa only [Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left U positive
  have cube : U^2 ≤ U^3 := by nlinarith [Nat.mul_le_mul_left (U^2) positive]
  have input : callerSize contents ≤ U^3 := by
    have smaller : callerSize contents ≤ U := by dsimp only [U]; omega
    exact smaller.trans (square.trans cube)
  calc
    spaceBudget contents ≤ U^3 + PDROC.BitVM.Common.sourcePushCap program Finset.univ *
        (callerTimeCoefficient * U^3) :=
      Nat.add_le_add input (Nat.mul_le_mul_left _ (timeBudget_callerCubic contents))
    _ = callerSpaceCoefficient * (callerSize contents + 1)^3 := by
      unfold callerSpaceCoefficient
      dsimp only [U]
      ring

/-- Exactly one global run from001 is selected. Its clock, original
source projection, final bytes,28-stack caller frame and ALL actual
physical-space states remain on that SAME witness. -/
theorem runs_resources (cells : List Cell) (contents : Stack → List Bool) (store : SourceStore)
    (outputWord : contents 22 = (cells.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate cells.length true) :
    ∃ (run : List State) (after : State),
      run.head? = some (before contents store) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧ after.l = none ∧
      after.stk 0 = encodeBits cells ∧ after.stk 22 = [] ∧ after.stk 24 = [] ∧ after.stk 23 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → after.stk other = contents other) ∧
      run.length ≤ timeBudget contents ∧
      (run.map (Lift.cfg embedding)).IsChain (fun a b => TM2.step OutputList.finalProgram a = some b) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBudget contents := by
  obtain ⟨run, after, head, chain, last, halt, halted, encoded, output, scratch, ticks, frame, time, clock⟩ :=
    runs cells contents store outputWord outputTicks
  refine ⟨run, after, head, chain, last, halt, halted, encoded, output, scratch, ticks, frame, time, clock, ?_⟩
  cases run with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons start rest =>
    have first : start = before contents store := Option.some.inj head
    have initial : ∀ role, (start.stk role).length ≤ callerSize contents := by
      rw [first]
      exact RatMarshal.initial_le_globalSize contents
    have supported : start.l ∈ Finset.insertNone (Finset.univ : Finset Label) := by
      rw [first]
      exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)
    have bounded := PDROC.BitVM.Common.source_path_occupancy program Finset.univ supports start rest
      (callerSize contents) supported initial chain
    have length : rest.length ≤ timeBudget contents := by
      simp only [List.length_cons] at time
      omega
    intro state member role
    exact ((bounded state member).2 role).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.Finalize
