module

public import Structure.PA06_A19Prepare_PackedCost049
public import Structure.PA06_A19Prepare_Entry_003
public import Structure.PA06_A19Prepare_ControlBank017_Geometry
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! Original loading/allocation/trace charges from an actual step bound.
This is a scalar cost lemma, not existence of a correct preprocessor.
No positive-stage assumption is used. Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCostBudget051

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine CompactControllerClaims

theorem work_facts (N q t : Nat) (ht : 0 < t) :
    1 ≤ work N q t ∧ q ≤ work N q t ∧ t ≤ work N q t ∧
      N + q + 1 ≤ work N q t := by
  let base := (N + 1) * (q + 1)
  have hbase : 1 ≤ base := by
    change 0 < (N + 1) * (q + 1)
    exact Nat.mul_pos (by omega) (by omega)
  have hbaseWork : base ≤ work N q t := by
    change base ≤ base * t
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left base (by omega : 1 ≤ t)
  have htWork : t ≤ work N q t := by
    change t ≤ base * t
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right t hbase
  have hmassBase : N + q + 1 ≤ base := by
    dsimp only [base]
    nlinarith [Nat.zero_le (N * q)]
  have hmassWork := hmassBase.trans hbaseWork
  exact ⟨by omega, (by omega : q ≤ N + q + 1).trans hmassWork, htWork, hmassWork⟩

theorem capacity_le_work (N q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    capacityWords 8192 N q t ≤ 16393 * work N q t := by
  have facts := work_facts N q t ht
  have hq2 : q + 2 ≤ 2 * (q + 1) := by omega
  have ht2 : t + 1 ≤ 2 * t := by omega
  have table : tableWords N q t ≤ 4 * work N q t := by
    calc
      tableWords N q t = (N + 1) * (q + 2) * (t + 1) := rfl
      _ ≤ ((N + 1) * (2 * (q + 1))) * (2 * t) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left (N + 1) hq2) ht2
      _ = 4 * work N q t := by unfold work; ring
  have scratch : 8192 * (t + 1) ≤ 16384 * work N q t := by
    calc
      8192 * (t + 1) ≤ 8192 * (2 * t) := Nat.mul_le_mul_left 8192 ht2
      _ = 16384 * t := by ring
      _ ≤ 16384 * work N q t := Nat.mul_le_mul_left 16384 facts.2.2.1
  rw [capacityWords, ite_eq_right (Nat.ne_of_gt hq)]
  calc
    tableWords N q t + q + 8192 * (t + 1) ≤
        4 * work N q t + work N q t + 16384 * work N q t :=
      Nat.add_le_add (Nat.add_le_add table facts.2.1) scratch
    _ = 16389 * work N q t := by ring
    _ ≤ 16393 * work N q t :=
      Nat.mul_le_mul_right (work N q t) (by decide : 16389 ≤ 16393)

theorem source_size_le_work (N q t : Nat) (ht : 0 < t) :
    N * q + q + 2 ≤ 3 * work N q t := by
  have facts := work_facts N q t ht
  have base : (N + 1) * (q + 1) ≤ work N q t := by
    unfold work
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left ((N + 1) * (q + 1)) (by omega : 1 ≤ t)
  have linear : N * q + q + 2 ≤ (N + 1) * (q + 1) + 1 := by nlinarith
  omega

theorem allocation_le_work (N q t : Nat) (hq : 0 < q) (ht : 0 < t) :
    PA06A19PrepareControlBank017.allocation N q t
      (packedCapacityWords q (capacityWords 8192 N q t) (indexWidth 32 N q)) ≤
        32781 * work N q t := by
  have facts := work_facts N q t ht
  have packed := (PA06A19PreparePackedCost049.actual_packedCapacityWords_le_capacity N q t).trans
    (capacity_le_work N q t hq ht)
  have dimensions : N + q + 1 + t ≤ 2 * work N q t := by omega
  unfold PA06A19PrepareControlBank017.allocation PA06A19PrepareControlBank017.dimensions
    PA06A19PrepareControlBank017.mass
  omega

/-- P and S may be fixed before the original inputs. The only execution
input here is the lower-level step bound; neither DRC nor HeapRepresents
nor existence of P is assumed or concluded by this cost-only lemma. -/
theorem totalCost_le_of_steps (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (program : List PackingOp) (steps S : Nat)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (hq : 0 < q)
    (hsteps : steps ≤ S * preprocessingWork full.length q (treeSize q full)) :
    totalCost
      (PA06A19PrepareControlBank017.allocation full.length q (treeSize q full)
        (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)))
      (controllerInput q full used) program steps heap ≤
      (12 * S + 32792 + (packingCode program).length) *
        preprocessingWork full.length q (treeSize q full) := by
  let W := work full.length q (treeSize q full)
  let R := preprocessingWork full.length q (treeSize q full)
  let K := (packingCode program).length
  have ht := PA06A19PrepareControlBank017.treeSize_pos full hq
  have facts := work_facts full.length q (treeSize q full) ht
  have hWR : W ≤ R := by
    dsimp only [W, R]
    rw [preprocessingWork, ite_eq_right (Nat.ne_of_gt hq)]
    omega
  have hR : 1 ≤ R := facts.1.trans hWR
  have hrom : (controllerInput q full used).size ≤ 3 * R := by
    rw [PA06A19PrepareEntry003.controllerInput_size]
    exact (source_size_le_work full.length q (treeSize q full) ht).trans
      (Nat.mul_le_mul_left 3 hWR)
  have hheap : PA06A19PrepareControlBank017.allocation full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q)) ≤ 32781 * R :=
    (allocation_le_work full.length q (treeSize q full) hq ht).trans
      (Nat.mul_le_mul_left 32781 hWR)
  have hcode : K ≤ K * R := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left K hR
  have hstartup : 8 ≤ 8 * R := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 8 hR
  have htrace : (packingDynamicTrace (controllerInput q full used) program steps
      (packingInitial heap)).length ≤ (12 * S) * R := by
    calc
      _ ≤ 12 * steps := packingDynamicTrace_length_le _ _ _ _
      _ ≤ 12 * (S * R) := Nat.mul_le_mul_left 12 hsteps
      _ = (12 * S) * R := by ring
  unfold totalCost
  change (controllerInput q full used).size + K + _ + 8 + _ ≤ (12 * S + 32792 + K) * R
  calc
    _ ≤ 3 * R + K * R + 32781 * R + 8 * R + (12 * S) * R :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hrom hcode) hheap) hstartup) htrace
    _ = (12 * S + 32792 + K) * R := by ring

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCostBudget051
