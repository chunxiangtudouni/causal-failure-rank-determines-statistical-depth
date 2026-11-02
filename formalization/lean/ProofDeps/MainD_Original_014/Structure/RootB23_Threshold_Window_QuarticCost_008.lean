module

public import Structure.RootB23_Threshold_Window_Power_007

@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow

open Turing PSTRTMSeq005

theorem quartic_fee_eq (k n gap : Nat) :
    powerFee k n 4 gap =
      2 * gap * n ^ 4 + 2 * k * n ^ 8 + 2 * k * n ^ 7 + 2 * k * n ^ 6 +
      2 * k * n ^ 5 + 4 * k * n ^ 4 + 8 * n ^ 5 + 35 * n ^ 4 +
      32 * n ^ 3 + 32 * n ^ 2 + 24 * n + 6 := by
  simp only [powerFee]
  ring

theorem quartic_fee_le (k n gap : Nat) :
    powerFee k n 4 gap ≤ (16 * k + 256) * (n + gap + 1) ^ 8 := by
  let room := n + gap + 1
  have positive : 1 ≤ room := by unfold room; omega
  have nRoom : n ≤ room := by unfold room; omega
  have gRoom : gap ≤ room := by unfold room; omega
  have powers : ∀ e ≤ 8, n ^ e ≤ room ^ 8 := by
    intro e eight
    exact (Nat.pow_le_pow_left nRoom e).trans (Nat.pow_le_pow_right positive eight)
  have p2 := powers 2 (by decide)
  have p3 := powers 3 (by decide)
  have p4 := powers 4 (by decide)
  have p5 := powers 5 (by decide)
  have k4 := Nat.mul_le_mul_left k p4
  have k5 := Nat.mul_le_mul_left k p5
  have k6 := Nat.mul_le_mul_left k (powers 6 (by decide))
  have k7 := Nat.mul_le_mul_left k (powers 7 (by decide))
  have k8 := Nat.mul_le_mul_left k (powers 8 (by decide))
  have linear : n ≤ room ^ 8 := by simpa only [pow_one] using powers 1 (by decide)
  have one : 1 ≤ room ^ 8 := by
    simpa only [pow_zero] using Nat.pow_le_pow_right positive (by decide : 0 ≤ 8)
  have gapTerm : gap * n ^ 4 ≤ room ^ 8 := by
    calc
      _ ≤ room * room ^ 4 := Nat.mul_le_mul gRoom (Nat.pow_le_pow_left nRoom 4)
      _ = room ^ 5 := by ring
      _ ≤ _ := Nat.pow_le_pow_right positive (by decide : 5 ≤ 8)
  rw [quartic_fee_eq]
  change _ ≤ (16 * k + 256) * room ^ 8
  nlinarith

/-- The closed depth-four program, with one actual trace, unchanged whole
archive, a true final home/HALT, and explicit fixed polynomial time/space. -/
theorem quartic_gap_polynomial (k : Nat) (archive : List Bool) (n gap : Nat) :
    ∃ trace, RunsFrom (powerMachine k 4)
      ⟨0, Tape.mk₂ (false :: archive) (powerWord n 4 gap)⟩ trace
      ⟨powerExit k 4, Tape.mk₂ (false :: archive) (powerWord n 4 (gap + k * n ^ 4))⟩ ∧
      trace.length ≤ (16 * k + 256) * (n + gap + 1) ^ 8 ∧
      ∀ inputLength clock,
        visitedSpace (powerMachine k 4) inputLength (trace.take clock) ≤
          inputLength + 2 * ((16 * k + 256) * (n + gap + 1) ^ 8) + 1 := by
  obtain ⟨trace, run, time, space⟩ := quartic_gap_runsFrom k archive n gap
  have budget := quartic_fee_le k n gap
  refine ⟨trace, run, time.trans budget, ?_⟩
  intro inputLength clock
  exact (space inputLength clock).trans (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow
