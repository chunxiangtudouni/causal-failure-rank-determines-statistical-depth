module

public import Structure.PA06_A19Prepare_CostBudget051
public import Structure.PA06_A19Prepare_PreBuild044_Layout
public import Structure.PA06_A19Prepare_InitialUsed037
public import PaperProofs.Structure.RawIncidenceCostBounds
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! Scalar bounds for the clocks of the actual positive-tool preparation.
These lemmas do not assert that a run exists or that it represents the
controller. In particular they cannot discharge RawPreprocessorObligation
without the separately constructed same-program execution. N=0 is allowed.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStepBudget053

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims

private theorem tree_work_facts (N q : Nat) (hq : 0 < q) :
    1 ≤ treeWork N q ∧ N + q + 1 ≤ treeWork N q ∧
      N ≤ treeWork N q ∧ q ≤ treeWork N q := by
  let M := N + q + 1
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have hs : M ≤ M ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left M hm
  have hq' : 1 ≤ q := by omega
  have hs' : M ^ 2 ≤ treeWork N q := by
    change M ^ 2 ≤ M ^ 2 * q
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M ^ 2) hq'
  have hmass : N + q + 1 ≤ treeWork N q := hs.trans hs'
  exact ⟨hm.trans hmass, hmass, (by omega : N ≤ N + q + 1).trans hmass,
    (by omega : q ≤ N + q + 1).trans hmass⟩

theorem parentClockBound_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareCompactCandidates007.parentClockBound q full ≤
      6601 * treeWork full.length q := by
  let N := full.length
  let M := N + q + 1
  let T := treeWork N q
  let t := treeSize q full
  have facts := tree_work_facts N q hq
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have ht : t ≤ M := by
    have bound := PA06A19PrepareControlBank017.treeSize_bound full
    change t + 1 ≤ M + 1 at bound
    omega
  have hsize : (prepareNormalization q full).indexed.nodes.size = t := by
    simp only [t, treeSize, Nat.ne_of_gt hq, ite_false]
  have hq2 : q + 1 ≤ 2 * q := by omega
  have hm2 : M + 1 ≤ 2 * M := by omega
  have ht2 : t + 1 ≤ 2 * M := by omega
  have square : M ^ 2 ≤ T := by
    change M ^ 2 ≤ M ^ 2 * q
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M ^ 2) (by omega : 1 ≤ q)
  have check : checkerSteps N q ≤ 144 * T := checkerSteps_le N q hq
  have retention : RawCandidateRetentionRAM.totalSteps N q ≤ 1024 * T := by
    calc
      _ ≤ 512 * M ^ 2 * (q + 1) := RawCandidateRetentionRAM.totalSteps_le N q
      _ ≤ 512 * M ^ 2 * (2 * q) := Nat.mul_le_mul_left (512 * M ^ 2) hq2
      _ = 1024 * T := by dsimp only [T, treeWork, M]; ring
  have order : RawCandidateOrderingRAM.totalSteps M ≤ 1320 * T := by
    have hs : (M + 1) ^ 2 ≤ (2 * M) ^ 2 := by nlinarith
    calc
      _ ≤ 330 * (M + 1) ^ 2 := RawCandidateOrderingRAM.totalSteps_quadratic M
      _ ≤ 330 * (2 * M) ^ 2 := Nat.mul_le_mul_left 330 hs
      _ = 1320 * M ^ 2 := by ring
      _ ≤ 1320 * T := Nat.mul_le_mul_left 1320 square
  have parents : 512 * (t + 1) * (N + q + 2) * (q + 1) ≤ 4096 * T := by
    have hmass2 : N + q + 2 ≤ 2 * M := by dsimp only [M]; omega
    calc
      _ ≤ (512 * (2 * M)) * (2 * M) * (2 * q) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 512 ht2) hmass2) hq2
      _ = 4096 * T := by dsimp only [T, treeWork, M]; ring
  unfold PA06A19PrepareCompactCandidates007.parentClockBound
  rw [hsize]
  change checkerSteps N q + 17 + RawCandidateRetentionRAM.totalSteps N q +
    RawCandidateOrderingRAM.totalSteps M + 512 * (t + 1) * (N + q + 2) * (q + 1) ≤ 6601 * T
  have hT : 1 ≤ T := facts.1
  have overhead : 17 ≤ 17 * T := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 17 hT
  calc
    _ ≤ 144 * T + 17 * T + 1024 * T + 1320 * T + 4096 * T :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add check overhead) retention) order) parents
    _ = 6601 * T := by ring

theorem headerClock_le (N q : Nat) (hq : 0 < q) :
    PA06A19PrepareRawHeader039Body.headerClock N q ≤ 120 * treeWork N q := by
  have dimension := PA17UniformGenerator035i.dimensionClock_le N q
  have facts := tree_work_facts N q hq
  have linear : 6 * N + 12 * q + 102 ≤ 120 * (N + q + 1) := by omega
  have bound : PA06A19PrepareRawHeader039Body.headerClock N q ≤ 120 * (N + q + 1) := by
    unfold PA06A19PrepareRawHeader039Body.headerClock PA06A19PrepareHeaderScratch024.clock
      PA06A19PrepareRuntimeHeader019.clock
    rw [PA06A19PrepareRuntimeHeader019.postamble_length]
    omega
  exact bound.trans (Nat.mul_le_mul_left 120 facts.2.1)

theorem sequenceClock_le (N q : Nat) (hq : 0 < q) :
    PA06A19PrepareRuntimeLayout026.sequenceClock N q ≤ 361 * treeWork N q := by
  have facts := tree_work_facts N q hq
  rw [PA06A19PrepareRuntimeLayout026.sequenceClock_eq]
  unfold PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass
  omega

theorem childrenClock_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PrepareChildrenCache023.totalSteps q full ≤ 800 * treeWork full.length q := by
  let M := full.length + q + 1
  have size : PA06A19PrepareChildrenCache023.preparedSize q full ≤ M :=
    prepared_indexed_size_le q full
  have hm : 1 ≤ M := by dsimp only [M]; omega
  have ht2 : PA06A19PrepareChildrenCache023.preparedSize q full + 1 ≤ 2 * M := by omega
  have square : (PA06A19PrepareChildrenCache023.preparedSize q full + 1) ^ 2 ≤ (2 * M) ^ 2 := by
    nlinarith
  have workSquare : M ^ 2 ≤ treeWork full.length q := by
    change M ^ 2 ≤ M ^ 2 * q
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M ^ 2) (by omega : 1 ≤ q)
  calc
    _ ≤ 200 * (PA06A19PrepareChildrenCache023.preparedSize q full + 1) ^ 2 :=
      PA06A19PrepareChildrenCache023.totalSteps_le q full
    _ ≤ 200 * (2 * M) ^ 2 := Nat.mul_le_mul_left 200 square
    _ = 800 * M ^ 2 := by ring
    _ ≤ 800 * treeWork full.length q := Nat.mul_le_mul_left 800 workSquare

theorem clearClock_le (N q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    PA06A19PrepareClearVM045.clock N q t ≤ 115077 * work N q t := by
  have facts := PA06A19PrepareCostBudget051.work_facts N q t ht
  have packed := (PA06A19PreparePackedCost049.actual_packedCapacityWords_le_capacity N q t).trans
    (PA06A19PrepareCostBudget051.capacity_le_work N q t hq ht)
  have hN : N ≤ work N q t := (by omega : N ≤ N + q + 1).trans facts.2.2.2
  have ordinary : PA06A19PrepareFiniteClear031Setup.ordinaryWords N q t ≤ 40 * work N q t := by
    unfold PA06A19PrepareFiniteClear031Setup.ordinaryWords
    omega
  rw [PA06A19PrepareClearVM045.clock_eq]
  unfold PA06A19PrepareFiniteInit032.clearLength
  omega

theorem preBuildClock_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PA06A19PreparePreBuild044.clockBound q full ≤
      8192 * treeWork full.length q + 115077 * work full.length q (treeSize q full) := by
  have parent := parentClockBound_le q full hq
  have header := headerClock_le full.length q hq
  have sequence := sequenceClock_le full.length q hq
  have children := childrenClock_le q full hq
  have clear := clearClock_le full.length q (treeSize q full) hq
    (PA06A19PrepareControlBank017.treeSize_pos full hq)
  unfold PA06A19PreparePreBuild044.clockBound
  omega

/-- A fixed scalar, independent of q, N, full, the initial used set and all
actual run witnesses. F will be the fixed fullBuild AST budget factor. -/
def stepFactor (F : Nat) : Nat := 131072 + 32768 * F

/-- Only combines lower-level clocks. Its conclusion is a scalar inequality,
not dynamic correctness or existence of the fixed preprocessing program. -/
theorem preparation_steps_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (F beforeSteps buildSteps metadataSteps : Nat)
    (hbefore : beforeSteps ≤ PA06A19PreparePreBuild044.clockBound q full)
    (hbuild : buildSteps ≤ 64 + (32768 * F) * work full.length q (treeSize q full))
    (hmetadata : metadataSteps ≤ 1000 * treeWork full.length q) :
    beforeSteps + buildSteps + metadataSteps + PA06A19PrepareInitialUsed037.clock q + 24 + 1 ≤
      stepFactor F * preprocessingWork full.length q (treeSize q full) := by
  let T := treeWork full.length q
  let W := work full.length q (treeSize q full)
  have ht := PA06A19PrepareControlBank017.treeSize_pos full hq
  have facts := PA06A19PrepareCostBudget051.work_facts full.length q (treeSize q full) ht
  have before : beforeSteps ≤ 8192 * T + 115077 * W := hbefore.trans (preBuildClock_le q full hq)
  have used : PA06A19PrepareInitialUsed037.clock q ≤ 140 * W := by
    unfold PA06A19PrepareInitialUsed037.clock
    omega
  have small : 64 + 24 + 1 ≤ 89 * W := by omega
  have assembled : beforeSteps + buildSteps + metadataSteps + PA06A19PrepareInitialUsed037.clock q + 24 + 1 ≤
      9192 * T + (115306 + 32768 * F) * W := by
    have build : buildSteps ≤ 64 + (32768 * F) * W := hbuild
    have metadata : metadataSteps ≤ 1000 * T := hmetadata
    calc
      _ ≤ (8192 * T + 115077 * W) + (64 + (32768 * F) * W) +
          1000 * T + 140 * W + 24 + 1 :=
        Nat.add_le_add (Nat.add_le_add
          (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add before build) metadata) used)
          (Nat.le_refl 24)) (Nat.le_refl 1)
      _ = 9192 * T + 115217 * W + (32768 * F) * W + (64 + 24 + 1) := by ring
      _ ≤ 9192 * T + 115217 * W + (32768 * F) * W + 89 * W :=
        Nat.add_le_add (Nat.le_refl _) small
      _ = 9192 * T + (115306 + 32768 * F) * W := by ring
  have left : 9192 * T ≤ stepFactor F * T := Nat.mul_le_mul_right T (by unfold stepFactor; omega)
  have right : (115306 + 32768 * F) * W ≤ stepFactor F * W :=
    Nat.mul_le_mul_right W (by unfold stepFactor; omega)
  calc
    _ ≤ 9192 * T + (115306 + 32768 * F) * W := assembled
    _ ≤ stepFactor F * T + stepFactor F * W := Nat.add_le_add left right
    _ = stepFactor F * (T + W) := by ring
    _ = stepFactor F * preprocessingWork full.length q (treeSize q full) := by
      simp only [preprocessingWork, Nat.ne_of_gt hq, ite_false, T, W]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStepBudget053
