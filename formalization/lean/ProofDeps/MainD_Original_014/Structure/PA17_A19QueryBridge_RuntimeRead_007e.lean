module

public import Structure.PA17_A19QueryBridge_RuntimeRead_007d
public import Structure.PA17_A19QueryBridge_Numeric_006b

/-! The fixed cached reader at ORIGINAL A19 word/allocation formulas. All
primitive numeric conditions are discharged here. Remaining entry data are
the same-call cache/header/scalar representations produced by preparation,
not new original caller eligibility or an already-computed query answer. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem original_cached_read {q origin : Nat} (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (scratchFactor indexFactor : Nat)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp)
    (em : CachedEmbedded (indexWidth 32 full.length q) origin containing)
    (state : WordState (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords scratchFactor full.length q (treeSize q full)) configuration state.heap)
    (hscalar : (state.register .value).toNat < capacityWords scratchFactor full.length q (treeSize q full))
    (hwidth : state.heap (BitVec.ofNat _ (PSTRQueryLayout.physicalWorkspace full
        (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q) + 12)) =
      BitVec.ofNat _ (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat _ (PSTRQueryLayout.physicalWorkspace full
        (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q) + 13)) =
      lowMask _ (CapacityBits.width q))
    (hh : state.register .address = BitVec.ofNat _
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full
        (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q)) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat _ (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing 58 state
    after.halted = false ∧ after.pc = BitVec.ofNat _ (5 * (origin + 58)) ∧
    after.register .address = BitVec.ofNat _
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full
        (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q)) (treeSize q full)) ∧
    (after.register .value).toNat = logicalHeap q
      (capacityWords scratchFactor full.length q (treeSize q full)) state.heap (state.register .value).toNat ∧
    after.heap = state.heap := by
  have hr := PA17A19QueryBridgeNumeric006b.rank_allocated (bits := indexWidth 32 full.length q) full
    (capacityWords scratchFactor full.length q (treeSize q full)) indexFactor hq hl h64
  exact actual_cached_read em full command configuration _
    (physicalHeaderWords + packedCapacityWords q
      (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q) +
      indexFactor * (full.length + q + treeSize q full + 1)) state
    (PA17A19QueryBridgeNumeric006b.bits_eight full.length q) hq
    (PA17PackingBounds043.width_le_bits full.length q) rep hscalar
    (PA17A19QueryBridgeNumeric006b.scalar_room full scratchFactor hs)
    (PA17A19QueryBridgeNumeric006b.heap_room full scratchFactor indexFactor hs hi)
    (by omega) hwidth hmask hh hp ha

theorem prefix_represents {bits q origin : Nat} {containing : List PackingOp}
    (em : CachedEmbedded bits origin containing) (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 58) :
    HeapRepresents q full capWords configuration
      (packingRun (callInput q full command) containing count state).heap := by
  rw [cached_actual_prefix_heap em _ state hp ha count hc]
  exact rep

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRead007
