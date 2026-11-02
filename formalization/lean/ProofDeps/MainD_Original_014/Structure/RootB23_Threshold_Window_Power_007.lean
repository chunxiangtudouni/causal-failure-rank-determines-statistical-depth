module

public import Structure.RootB23_Threshold_Window_FieldLoop_006
public import Structure.PA17_TM_RatArithmetic_Allocate_013f

/-! A closed finite-code power allocator. Every internal inner-run contract is
discharged recursively, ending with the real013f expandMachine. Runtime n and
the gap do not occur in code. At fixed depth4 it grows exactly k*n^4 cells. -/

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005 PA17TMDivisionCompose006 PA17TMRatArithmeticAllocate013

def powerStates (k : Nat) : Nat → Nat
  | 0 => expandCap k
  | depth + 1 => fieldCap (powerStates k depth)

def powerExit (k : Nat) : (depth : Nat) → Fin (powerStates k depth + 1)
  | 0 => (expandLast k 0 []).q
  | depth + 1 => fieldExit (powerStates k depth)

def powerMachine (k : Nat) : (depth : Nat) → Machine (powerStates k depth)
  | 0 => expandMachine k
  | depth + 1 => fieldMachine (powerMachine k depth) (powerExit k depth)

def powerWord (n : Nat) : Nat → Nat → List Bool
  | 0, gap => false :: (List.replicate gap false ++ [true])
  | depth + 1, gap => pairs true n ++ false :: false :: powerWord n depth gap

def powerFee (k n : Nat) : Nat → Nat → Nat
  | 0, gap => 2 * gap + 4 * k + 9
  | depth + 1, gap =>
      n * (powerFee k n depth (gap + k * n ^ (depth + 1)) + 8 * n + 18) + 6

attribute [local implicit_reducible] powerStates

theorem powerFee_mono (k n depth left right : Nat) (ordered : left ≤ right) :
    powerFee k n depth left ≤ powerFee k n depth right := by
  induction depth generalizing left right with
  | zero => simp only [powerFee]; omega
  | succ depth ih =>
    have larger := ih (left + k * n ^ (depth + 1)) (right + k * n ^ (depth + 1)) (by omega)
    simp only [powerFee]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left n (Nat.add_le_add_right larger (8 * n + 18))) 6

/-- No inner execution remains as a hypothesis. All calls are to the chosen
finite machine at the preceding fixed code depth and ultimately to013f. -/
theorem power_run_contract (k n depth : Nat) :
    InnerRunContract (powerMachine k depth) (powerExit k depth) (powerWord n depth)
      (k * n ^ depth) (powerFee k n depth) := by
  induction depth with
  | zero =>
    intro archive gap
    have run := expand_runsFrom k gap (false :: archive)
    rw [expand_first_zero] at run
    have finalShape : expandLast k gap (false :: archive) =
        (⟨powerExit k 0, Tape.mk₂ (false :: archive)
          (powerWord n 0 (gap + k * n ^ 0))⟩ : MachineState (expandCap k)) := by
      simp only [powerExit, powerWord, pow_zero, Nat.mul_one, expandLast, expandLift,
        blockCfg, padCfg, seekState]
      rw [Nat.add_comm k gap]
      rfl
    rw [finalShape] at run
    refine ⟨expandTrace k gap (false :: archive), run, ?_⟩
    simp only [expand_length, powerFee]
    exact Nat.le_refl _
  | succ depth ih =>
    intro archive gap
    obtain ⟨trace, run, time, _⟩ := field_loop_runsFrom (powerMachine k depth) (powerExit k depth)
      (powerWord n depth) (k * n ^ depth) (powerFee k n depth) ih archive n gap
    have product : (k * n ^ depth) * n = k * n ^ (depth + 1) := by rw [pow_succ]; ring
    have actual : RunsFrom (powerMachine k (depth + 1))
        ⟨0, Tape.mk₂ (false :: archive) (powerWord n (depth + 1) gap)⟩ trace
        ⟨powerExit k (depth + 1), Tape.mk₂ (false :: archive)
          (powerWord n (depth + 1) (gap + k * n ^ (depth + 1)))⟩ := by
      simpa only [powerMachine, powerExit, powerWord, product] using run
    have bound := fieldLoopCost_le_constant (powerFee k n depth) (k * n ^ depth) n 0 gap
      (powerFee k n depth (gap + (k * n ^ depth) * n))
      (fun index beforeEnd => powerFee_mono k n depth index _ beforeEnd)
    refine ⟨trace, actual, time.trans ?_⟩
    simpa only [powerFee, product, Nat.add_zero, Nat.mul_zero] using bound

/-- One fixed program before every runtime counter width and original
archive, with a real final home and HALT. Four equal-width counted fields are
physical input here; their original-packet production is a separate real
caller obligation and is not silently granted as original input. -/
theorem quartic_gap_runsFrom (k : Nat) (archive : List Bool) (n gap : Nat) :
    ∃ trace, RunsFrom (powerMachine k 4)
      ⟨0, Tape.mk₂ (false :: archive) (powerWord n 4 gap)⟩ trace
      ⟨powerExit k 4, Tape.mk₂ (false :: archive) (powerWord n 4 (gap + k * n ^ 4))⟩ ∧
      trace.length ≤ powerFee k n 4 gap ∧
      ∀ inputLength clock,
        visitedSpace (powerMachine k 4) inputLength (trace.take clock) ≤
          inputLength + 2 * powerFee k n 4 gap + 1 := by
  obtain ⟨trace, run, time⟩ := power_run_contract k n 4 archive gap
  refine ⟨trace, run, time, ?_⟩
  intro inputLength clock
  have general := PSTRTMTrace002.visitedSpace_le (powerMachine k 4) inputLength (trace.take clock)
  have taken : (trace.take clock).length ≤ trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
