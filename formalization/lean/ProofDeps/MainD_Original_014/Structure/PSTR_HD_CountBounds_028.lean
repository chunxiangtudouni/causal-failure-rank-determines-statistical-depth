module

public import Structure.PSTR_HD_CountEntry_027
public import PaperProofs.Structure.IndexedUsedCounts
public import PaperProofs.Structure.PackingWordBounds
import Mathlib.Tactic.Ring

/-! Numeric and mathematical invariants for the actual fixed child loop.
prefixSum is a specification of reads from the real physical scratch array,
not an operation available to the runtime program. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PSTRStaticLayout PSTRCountWorkspace

def prefixSum {bits q : Nat} (full : List (Finset (Fin q)))
    (heap : BitVec bits → BitVec bits) (countsBase offset count : Nat) : Nat :=
  ((List.range count).map (fun position =>
    (heap (BitVec.ofNat bits (countsBase + (PSTRStaticLayout.childWords q full).getD (offset + position) 0))).toNat)).sum

theorem prefixSum_succ {bits q : Nat} (full : List (Finset (Fin q)))
    (heap : BitVec bits → BitVec bits) (countsBase offset count : Nat) :
    prefixSum full heap countsBase offset (count + 1) = prefixSum full heap countsBase offset count +
      (heap (BitVec.ofNat bits (countsBase + (PSTRStaticLayout.childWords q full).getD (offset + count) 0))).toNat := by
  simp [prefixSum, List.range_succ]

theorem prefixSum_le {bits q : Nat} (full : List (Finset (Fin q)))
    (heap : BitVec bits → BitVec bits) (countsBase offset count bound : Nat)
    (hc : ∀ position < count,
      (heap (BitVec.ofNat bits (countsBase + (PSTRStaticLayout.childWords q full).getD (offset + position) 0))).toNat ≤ bound) :
    prefixSum full heap countsBase offset count ≤ bound * count := by
  induction count with
  | zero => simp [prefixSum]
  | succ count ih =>
    have hp := ih (fun position hposition => hc position (by omega))
    have hn := hc count (by omega)
    rw [prefixSum_succ, Nat.mul_succ]
    omega

theorem q_times_size_fit (N q t : Nat) (ht : t ≤ N + q + 1) :
    Fits (indexWidth 32 N q) (q * t) := by
  apply fits_indexWidth_of_lt_power
  have hq : q ≤ N + q + 2 := by omega
  have ht' : t ≤ N + q + 2 := by omega
  have hm : q * t ≤ (N + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hq ht'
  have hsmall : (N + q + 2) ^ 2 < (N + q + 2) ^ 16 :=
    (Nat.le_add_right _ 1024).trans_lt (quadratic_add_lt_power16 (N + q + 2) (by omega))
  have hlarge : (N + q + 2) ^ 16 ≤ (N + q + 2) ^ 32 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  exact (hm.trans_lt hsmall).trans_le hlarge

theorem original_partial_sum_fit {q : Nat} (full : List (Finset (Fin q)))
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (countsBase offset count : Nat) (hcount : count ≤ (prepareNormalization q full).indexed.nodes.size)
    (hc : ∀ position < count,
      (heap (BitVec.ofNat (indexWidth 32 full.length q)
        (countsBase + (PSTRStaticLayout.childWords q full).getD (offset + position) 0))).toNat ≤ q) :
    Fits (indexWidth 32 full.length q) (prefixSum full heap countsBase offset count) := by
  have hs := prefixSum_le full heap countsBase offset count q hc
  exact (hs.trans (Nat.mul_le_mul_left q hcount)).trans_lt
    (q_times_size_fit full.length q _ (prepared_indexed_size_le q full))

theorem usedCount_bound {q : Nat} (cache : IndexedNodeCache (Fin q))
    (used : Finset (Fin q)) (node : cache.NodeId) :
    (IndexedDescent.usedCounts cache used).get node ≤ q := by
  rw [IndexedDescent.usedCounts_get]
  have hs : used ∩ cache.decode node ⊆ (Finset.univ : Finset (Fin q)) := by
    intro tool _
    exact Finset.mem_univ tool
  simpa using Finset.card_le_card hs

theorem canonical_counts_room {bits q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (capWords indexFactor : Nat) (hi : 32 ≤ indexFactor) :
    base q full capWords bits + 16 + (prepareNormalization q full).indexed.nodes.size <
      physicalHeaderWords + packedCapacityWords q capWords bits +
        indexFactor * (full.length + q + treeSize q full + 1) := by
  rw [base_metadata_end q full hq capWords bits, metadata_length q full hq, edgeCount_eq q full hq hl]
  have hm := Nat.mul_le_mul_right (full.length + q + treeSize q full + 1) hi
  simp only [treeSize, ne_of_gt hq, ite_false] at hm ⊢
  unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
  omega

theorem canonical_scratch_fit {bits q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (capWords indexFactor : Nat) (hi : 32 ≤ indexFactor)
    (hf : Fits bits (physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1))) :
    Fits bits (base q full capWords bits + 7) ∧
      Fits bits (base q full capWords bits + 16 + (prepareNormalization q full).indexed.nodes.size) := by
  have hr := canonical_counts_room (bits := bits) full hq hl capWords indexFactor hi
  exact ⟨(show base q full capWords bits + 7 ≤ base q full capWords bits + 16 +
      (prepareNormalization q full).indexed.nodes.size by omega).trans_lt (hr.trans hf), hr.trans hf⟩

end PaperProofs.Structure.LaminarTree.PSTRCountBounds
