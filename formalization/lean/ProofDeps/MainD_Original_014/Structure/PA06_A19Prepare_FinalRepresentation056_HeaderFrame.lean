module

public import Structure.PA06_A19Prepare_FinalHeader033
public import Structure.PA06_A19Prepare_StaticMetadata036_WordBounds

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED logical frames for the actual final24-op header writer.
The bitwise decoder only observes real packed words, not physical headers
or the stage/failed ordinary words. No125/055 endpoint is imported. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation056
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM

theorem logical_capacity_congr_words {bits : Nat} (q C : Nat) (hq : 0 < q) (hb : 0 < bits)
    (before after : BitVec bits → BitVec bits)
    (frame : ∀ point, 4 ≤ point → point < 4 + packedCapacityWords q C bits →
      after (BitVec.ofNat bits point) = before (BitVec.ofNat bits point))
    (address : Nat) (ha : address < C) :
    logicalHeap q C after address = logicalHeap q C before address := by
  simp only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq), unpackHeap, ha, ite_true]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext position
  have hm := Nat.mul_le_mul_right (CapacityBits.width q) (show address + 1 ≤ C by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  have hoff : address * CapacityBits.width q + position.val < C * CapacityBits.width q := by
    have hp := position.isLt
    omega
  have hd : (address * CapacityBits.width q + position.val) / bits < packedCapacityWords q C bits :=
    (Nat.div_lt_iff_lt_mul hb).mpr (hoff.trans_le (packedCapacityWords_mul_bits q C hb))
  rw [PA06A19PreparePackedView013.dataHeap_word, PA06A19PreparePackedView013.dataHeap_word,
    frame (4 + (address * CapacityBits.width q + position.val) / bits)
      (Nat.le_add_right 4 _) (Nat.add_lt_add_left hd 4)]

theorem logical_metadata_word {bits : Nat} (q C position : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) :
    logicalHeap q C heap (C + 2 + position) =
      (heap (BitVec.ofNat bits (6 + packedCapacityWords q C bits + position))).toNat := by
  have hn : ¬ C + 2 + position < C := by omega
  have hs : C + 2 + position - C = 2 + position := by omega
  simp only [logicalHeap, ite_eq_right (Nat.ne_of_gt hq), unpackHeap, hn, ite_false, hs,
    PA06A19PreparePackedView013.dataHeap_word]
  have he : 4 + (packedCapacityWords q C bits + (2 + position)) =
      6 + packedCapacityWords q C bits + position := by omega
  rw [he]

/-- The real033 frame suffices for all capacities and every ordinary
staticMetadata value, including stageNodes. Only live scalars C/C+1
(stage/failed) are excluded from this preservation statement. -/
theorem actual_header_logical_frame (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (left right : List PackingOp)
    (before : WordState (indexWidth 32 full.length q))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hbank : PA06A19PrepareFinalHeader033.BankData q full before)
    (hh : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ PA06A19PrepareFinalHeader033.program ++ right)))
    (hpcCode : Fits (indexWidth 32 full.length q)
      (5 * (left ++ PA06A19PrepareFinalHeader033.program ++ right).length)) :
    let C := capacityWords 8192 full.length q (treeSize q full)
    let after := packingRun (controllerInput q full used)
      (left ++ PA06A19PrepareFinalHeader033.program ++ right) 24 before
    (∀ address < C, logicalHeap q C after.heap address = logicalHeap q C before.heap address) ∧
    (∀ position < (staticMetadata q full).length,
      logicalHeap q C after.heap (C + 2 + position) = logicalHeap q C before.heap (C + 2 + position)) := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let C := capacityWords 8192 full.length q t
  let P := packedCapacityWords q C bits
  let after := packingRun (controllerInput q full used)
    (left ++ PA06A19PrepareFinalHeader033.program ++ right) 24 before
  have hP5Fit : Fits bits (P + 5) := by
    have hc := PA06A19PrepareRuntimeLayout026.actual_bank_field_fits q full hq 5 (by decide)
    have hle : P + 5 ≤ PA06A19PrepareControlBank017.controlBase full.length q t P + 5 := by
      unfold PA06A19PrepareControlBank017.controlBase
      omega
    exact hle.trans_lt hc
  have physical (point : Nat) (hf : Fits bits point)
      (h0 : point ≠ 0) (h1 : point ≠ 1) (h2 : point ≠ 2)
      (hstage : point ≠ P + 4) (hfailed : point ≠ P + 5) :
      after.heap (BitVec.ofNat bits point) = before.heap (BitVec.ofNat bits point) := by
    apply PA06A19PrepareFinalHeader033.actual_frame q full used hq left right before hpc ha hbank hh hcode hpcCode
    change point < 2 ^ bits at hf
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf]
    exact ⟨h0, h1, h2, hstage, hfailed⟩
  dsimp only
  constructor
  · intro address had
    apply logical_capacity_congr_words q C hq (PA17PackingBounds043.bits_pos full.length q)
      before.heap after.heap ?_ address had
    intro point hlow hhigh
    change point < 4 + P at hhigh
    exact physical point ((by omega : point ≤ P + 5).trans_lt hP5Fit)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro position hp
    rw [logical_metadata_word q C position after.heap hq, logical_metadata_word q C position before.heap hq]
    apply congrArg BitVec.toNat
    have fit := (PA06A19PrepareStaticMetadata036.actual_metadata_output_bounds q full hq hl).2.2 position hp
    have hP : PA06A19PrepareChildrenCache023.actualPackedWords q full = P := by
      simp only [PA06A19PrepareChildrenCache023.actualPackedWords, P, C, bits, t,
        treeSize, Nat.ne_of_gt hq, ite_false]
    have hfit : Fits bits (6 + P + position) := by simpa only [hP] using fit.2
    exact physical (6 + P + position) hfit (by omega) (by omega) (by omega) (by omega) (by omega)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation056
