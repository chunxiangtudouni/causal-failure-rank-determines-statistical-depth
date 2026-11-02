module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_Input_025a

/-! Original wordFactor32/shared allocation8192 discharge every selector
room/Fits/layout side condition. The only selected budget bound is the
natural range later obtained from the actual firstFalse rank field. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17A19RuntimeSelect009

theorem endpoint_layout (workspace q size : Nat) :
    PA17A19RuntimeSelect009.endpoint (PSTRQueryLayout.header workspace size) q size =
      PSTRQueryLayout.endpoint workspace size q := by
  unfold PA17A19RuntimeSelect009.endpoint PA17A19RuntimeSelect009.childBase PSTRQueryLayout.endpoint
    PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
  omega

theorem original_payload_bound {q : Nat} (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (budget : Nat) (hq : 0 < q) (hb : budget ≤ q + 1) :
    payloadBase (PA17A19RuntimeHeader011.row full stage) budget (treeSize q full) + treeSize q full ≤
      capacityWords 8192 full.length q (treeSize q full) := by
  have hr := PA17QueryBudget015.row_fits_table full.length q (treeSize q full) (PA17QueryBudget015.rowIndex full stage)
  have ht : tableWords full.length q (treeSize q full) ≤ capacityWords 8192 full.length q (treeSize q full) := by
    simp only [capacityWords, ne_of_gt hq, ite_false]
    omega
  have hm := Nat.mul_le_mul_right (treeSize q full + 1) (show budget + 1 ≤ q + 2 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  change PA17A19RuntimeHeader011.row full stage + (q + 2) * (treeSize q full + 1) ≤ tableWords full.length q (treeSize q full) at hr
  unfold payloadBase
  omega

theorem original_layout {q : Nat} (full : List (Finset (Fin q)))
    (stage : Fin (full.length + 1)) (budget : Nat) (hq : 0 < q) (hl : LaminarSchedule full)
    (hb : budget ≤ q + 1) :
    let bits := indexWidth 32 full.length q
    let C := capacityWords 8192 full.length q (treeSize q full)
    let words := physicalHeaderWords + packedCapacityWords q C bits + 8192 * (full.length + q + treeSize q full + 1)
    let W := PSTRQueryLayout.physicalWorkspace full C bits
    let H := PSTRQueryLayout.header W (treeSize q full)
    ReverseLayout bits q full C words H
      (payloadBase (PA17A19RuntimeHeader011.row full stage) budget (treeSize q full))
      (PSTRQueryLayout.countsBase W) (PSTRQueryLayout.parentsBase W (treeSize q full)) (treeSize q full) := by
  dsimp only
  let bits := indexWidth 32 full.length q
  let C := capacityWords 8192 full.length q (treeSize q full)
  let words := physicalHeaderWords + packedCapacityWords q C bits + 8192 * (full.length + q + treeSize q full + 1)
  let W := PSTRQueryLayout.physicalWorkspace full C bits
  have hs : Fits bits (4 + C * CapacityBits.width q) := PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)
  have hf : Fits bits words := PA17A19QueryBridgeNumeric006b.heap_room full 8192 8192 (by decide) (by decide)
  have ha : PSTRQueryLayout.endpoint W (treeSize q full) q ≤ words :=
    PSTRQueryLayout.endpoint_index_factor full C bits 8192 hq hl (by decide)
  have hw : 0 < CapacityBits.width q := by
    have hn := (CapacityBits.width_eq_zero_iff q).not.mpr (Nat.ne_of_gt hq)
    omega
  have hc : Fits bits C := (Nat.le_mul_of_pos_right C hw).trans_lt ((Nat.le_add_left _ 4).trans_lt hs)
  have hp := original_payload_bound full stage budget hq hb
  refine ⟨PA17A19QueryBridgeNumeric006b.bits_eight full.length q, hq, PA17PackingBounds043.width_le_bits full.length q,
    rfl, rfl, hs, hf, ?_, ?_, ?_, hp, hp.trans_lt hc, ?_, ?_⟩
  · rw [endpoint_layout]
    exact ha.trans_lt hf
  · rw [endpoint_layout]
    exact ha
  · simp only [capacityWords, ne_of_gt hq, ite_false]
    omega
  · unfold PSTRQueryLayout.header PSTRQueryLayout.parentsBase
    omega
  · unfold PSTRQueryLayout.header
    omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelectInput025
