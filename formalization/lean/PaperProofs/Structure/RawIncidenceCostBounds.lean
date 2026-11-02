module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.PackingExecutionCost
public import PaperProofs.Structure.PackingWordBounds
import Mathlib.Tactic.Linarith

/-! Cost and word-footprint adapters for the actual raw checker. A bound
on actual instruction steps is kept distinct from semantic correctness and
prefix safety; neither is assumed completed by these numeric estimates. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine

def checkerSteps (N q : Nat) : Nat := N ^ 2 * (53 * q + 47) + 26 * N + 18

theorem checkerSteps_le (N q : Nat) (hq : 0 < q) :
    checkerSteps N q ≤ 144 * treeWork N q := by
  let base := N + q + 1
  have hb : 1 ≤ base := by dsimp [base]; omega
  have hs : base ≤ base ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left base hb
  have hN : N ≤ base ^ 2 := (show N ≤ base by dsimp [base]; omega).trans hs
  have hq1 : 1 ≤ q := hq
  have hsq1 : 1 ≤ base ^ 2 := Nat.pow_le_pow_left hb 2
  have hunit : 1 ≤ base ^ 2 * q := Nat.mul_le_mul hsq1 hq1
  have hNwork : N ≤ base ^ 2 * q :=
    hN.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (base ^ 2) hq1)
  have hN2 : N ^ 2 * q ≤ base ^ 2 * q :=
    Nat.mul_le_mul_right q (Nat.pow_le_pow_left (show N ≤ base by dsimp [base]; omega) 2)
  have hfirst : N ^ 2 * (53 * q + 47) ≤ 100 * (base ^ 2 * q) := by
    calc
      _ ≤ N ^ 2 * (100 * q) := Nat.mul_le_mul_left _ (by omega)
      _ = 100 * (N ^ 2 * q) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 100 hN2
  change N ^ 2 * (53 * q + 47) + 26 * N + 18 ≤ 144 * (base ^ 2 * q)
  omega

theorem checker_numeric_total_le (N q : Nat) (hq : 0 < q) :
    N * q + 653 + 12 * checkerSteps N q ≤ 4096 * treeWork N q := by
  have hsteps := checkerSteps_le N q hq
  have hunit : 1 ≤ treeWork N q := by
    unfold treeWork
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : 1 ≤ N + q + 1) 2) hq
  have hN : N ≤ (N + q + 1) ^ 2 := by nlinarith
  have hNq : N * q ≤ treeWork N q := Nat.mul_le_mul_right q hN
  omega

theorem rawIncidenceROM_size (q : Nat) (full : List (Finset (Fin q))) :
    (rawIncidenceROM q full).size = full.length * q + 2 := by
  simp only [rawIncidenceROM, PhysicalROM.size, List.length_append, incidence_length,
    List.length_cons, List.length_nil]
  omega

theorem checker_totalCost_le {bits : Nat} (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (steps : Nat) (heap : BitVec bits → BitVec bits)
    (hsteps : steps ≤ checkerSteps full.length q) :
    totalCost 8 (rawIncidenceROM q full) checker steps heap ≤ 4096 * treeWork full.length q := by
  have htrace := packingDynamicTrace_length_le (rawIncidenceROM q full) checker steps (packingInitial heap)
  unfold totalCost
  rw [rawIncidenceROM_size, packingCode_length, checker_length]
  have hnum := checker_numeric_total_le full.length q hq
  omega

theorem checker_footprint_fits (q : Nat) (full : List (Finset (Fin q))) :
    Fits (indexWidth 16 full.length q)
      ((rawIncidenceROM q full).size + 8 + (packingCode checker).length) := by
  rw [rawIncidenceROM_size, packingCode_length, checker_length]
  exact fits_checker_footprint full.length q

end PaperProofs.Structure.LaminarTree.RawIncidenceLaminarRAM
