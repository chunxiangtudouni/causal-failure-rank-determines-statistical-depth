module

public import Structure.PA17_A19QueryBridge_RuntimeHeader_011e

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRStaticLayout PSTRStaticHeap PSTRWordSegments

/-- All data-arithmetic conditions needed by the fixed header follow from
the represented original capacity allocation. They are not new caller data. -/
theorem numeric_room {bits q : Nat} (full : List (Finset (Fin q))) (stage : Fin (full.length + 1))
    (capWords : Nat) (hq : 0 < q)
    (htable : tableWords full.length q (treeSize q full) ≤ capWords)
    (hscalar : Fits bits (4 + capWords * CapacityBits.width q)) :
    Fits bits full.length ∧ Fits bits (q + 2) ∧ Fits bits (treeSize q full + 1) ∧
      Fits bits ((stage.val + 1) * (q + 2)) ∧ Fits bits (row full stage) := by
  have hw : 0 < CapacityBits.width q := by
    have hn := (CapacityBits.width_eq_zero_iff q).not.mpr (Nat.ne_of_gt hq)
    omega
  have hc : Fits bits capWords :=
    (Nat.le_mul_of_pos_right capWords hw).trans_lt ((Nat.le_add_left _ 4).trans_lt hscalar)
  have htab : Fits bits (tableWords full.length q (treeSize q full)) := htable.trans_lt hc
  have hprod : (full.length + 1) * (q + 2) ≤ tableWords full.length q (treeSize q full) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hN : full.length < 2 ^ bits :=
    (show full.length ≤ full.length + 1 by omega).trans_lt
      ((Nat.le_mul_of_pos_right _ (by omega)).trans_lt (hprod.trans_lt htab))
  have hq2 : q + 2 < 2 ^ bits :=
    (Nat.le_mul_of_pos_left _ (by omega)).trans_lt (hprod.trans_lt htab)
  have ht : treeSize q full + 1 < 2 ^ bits := by
    have hp : 0 < (full.length + 1) * (q + 2) := Nat.mul_pos (by omega) (by omega)
    exact (Nat.le_mul_of_pos_left _ hp).trans_lt htab
  have hr : (stage.val + 1) * (q + 2) < 2 ^ bits := by
    have hh := Nat.mul_le_mul_right (q + 2) (show stage.val + 1 ≤ full.length + 1 from stage.isLt)
    exact hh.trans_lt (hprod.trans_lt htab)
  have hrow := PA17QueryBudget015.row_fits_table full.length q (treeSize q full) (PA17QueryBudget015.rowIndex full stage)
  exact ⟨hN, hq2, ht, hr, (Nat.le_add_right _ _).trans_lt (hrow.trans_lt htab)⟩

theorem original_numeric_room {q : Nat} (full : List (Finset (Fin q))) (stage : Fin (full.length + 1))
    (scratchFactor indexFactor : Nat) (hq : 0 < q) (hl : LaminarSchedule full)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (hi64 : 64 ≤ indexFactor) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1)
    Fits bits full.length ∧ Fits bits (q + 2) ∧ Fits bits (treeSize q full + 1) ∧
      Fits bits ((stage.val + 1) * (q + 2)) ∧ Fits bits (row full stage) ∧
      head full capWords bits + 3 < heapWords ∧ Fits bits (head full capWords bits + 3) := by
  dsimp only
  let capWords := capacityWords scratchFactor full.length q (treeSize q full)
  let bits := indexWidth 32 full.length q
  have htable : tableWords full.length q (treeSize q full) ≤ capWords := by
    simp only [capWords, capacityWords, ne_of_gt hq, ite_false]
    omega
  have hn := numeric_room full stage capWords hq htable
    (PA17A19QueryBridgeNumeric006b.scalar_room full scratchFactor hs)
  have hr := PA17A19QueryBridgeNumeric006b.rank_allocated (bits := bits) full capWords indexFactor hq hl hi64
  have hf := PA17A19QueryBridgeNumeric006b.heap_room full scratchFactor indexFactor hs hi
  have hh : head full capWords bits + 3 < physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1) := by
    change head full capWords bits + 16 + 2 * (q + 2) ≤ _ at hr
    omega
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, hh, hh.trans hf⟩

theorem storedHeap_values {bits : Nat} (heap : BitVec bits → BitVec bits) (header : Nat)
    (row node active stage : BitVec bits) (hf : Fits bits (header + 3)) :
    storedHeap heap header row node active stage (BitVec.ofNat bits header) = row ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 1)) = node ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 2)) = active ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 3)) = stage := by
  have hbound : header + 3 < 2 ^ bits := hf
  have hne (i j : Nat) (hi : i ≤ 3) (hj : j ≤ 3) (hne : i ≠ j) :
      BitVec.ofNat bits (header + i) ≠ BitVec.ofNat bits (header + j) := by
    intro he
    have hv := congrArg BitVec.toNat he
    rw [show (BitVec.ofNat bits (header + i)).toNat = header + i from Nat.mod_eq_of_lt (by omega),
      show (BitVec.ofNat bits (header + j)).toNat = header + j from Nat.mod_eq_of_lt (by omega)] at hv
    omega
  have hzero (j : Nat) (hj : j ≤ 3) (hz : j ≠ 0) :
      BitVec.ofNat bits header ≠ BitVec.ofNat bits (header + j) := by
    simpa only [Nat.add_zero] using hne 0 j (by omega) hj (Ne.symm hz)
  simpa only [Nat.add_zero] using (show
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 0)) = row ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 1)) = node ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 2)) = active ∧
    storedHeap heap header row node active stage (BitVec.ofNat bits (header + 3)) = stage from by
      simp +decide [storedHeap, hne, hzero])

theorem callCost_bound {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) : callCost q full program command 82 heap ≤ 1408 := by
  have ht := inline_trace_bound (callInput q full command) program (packingInitial heap)
  unfold callCost
  rw [packingCode_length, program_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeHeader011
