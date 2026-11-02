module

public import Structure.PA17_A19QueryBridge_RuntimeRanks_008g
public import Structure.PA17_A19QueryBridge_Numeric_006b
public import Structure.PSTR_RepairHeap_024

/-! The actual fixed rank loop preserves ORIGINAL HeapRepresents at EVERY
clock. Its internal materialized test flags are not new original caller
fields. All numeric/metadata/bitmap room is derived from the original A19
allocation with implementation constants fixed before the instance. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17A19QueryBridgeRankFrame012

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem original_rank_prefix_represents {q origin : Nat}
    (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (scratchFactor indexFactor : Nat) (hs : scratchFactor ≤ 65536)
    (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    let header := PSTRQueryLayout.header
      (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
    ∀ (_ : PA17A19RuntimeRanks008.Embedded bits origin containing) (state : WordState bits),
    HeapRepresents q full capWords configuration state.heap →
    ∀ good bad : Nat → Bool,
    (∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget)) =
      BitVec.ofNat bits (bit (good budget))) →
    (∀ budget < q + 2, state.heap (BitVec.ofNat bits (header + 16 + budget + (q + 2))) =
      BitVec.ofNat bits (bit (bad budget))) →
    state.register .address = BitVec.ofNat bits header →
    state.pc = BitVec.ofNat bits (5 * origin) → state.halted = false →
    ∀ clock ≤ PA17A19RuntimeRanks008.steps q,
      HeapRepresents q full capWords configuration
        (packingRun (callInput q full command) containing clock state).heap := by
  dsimp only
  intro em state rep good bad hgood hbad hh hp ha clock hc
  let capWords := capacityWords scratchFactor full.length q (treeSize q full)
  let bits := indexWidth 32 full.length q
  let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
    indexFactor * (full.length + q + treeSize q full + 1)
  let header := PSTRQueryLayout.header
    (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  have halloc : header + 16 + 2 * (q + 2) ≤ heapWords :=
    PA17A19QueryBridgeNumeric006b.rank_allocated full capWords indexFactor hq hl h64
  have hfit : Fits bits heapWords :=
    PA17A19QueryBridgeNumeric006b.heap_room full scratchFactor indexFactor hs hi
  have hroom : Fits bits (header + 16 + 2 * (q + 2)) := halloc.trans_lt hfit
  have hframe := PA17A19RuntimeRanks008.actual_leading_frame em (callInput q full command)
    q header heapWords good bad state hroom halloc
    (by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM]) rfl
    hgood hbad hh hp ha clock hc
  have hb : 0 < bits := PA17PackingBounds043.bits_pos full.length q
  have hbitmap : tableWords full.length q (treeSize q full) + q ≤ capWords := by
    dsimp only [capWords, capacityWords]
    rw [ite_eq_right (ne_of_gt hq)]
    omega
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (header + 4) state.heap _ hb hq rep hbitmap
    (PA17A19QueryBridgeNumeric006b.scalar_room full scratchFactor hs)
    ((show header + 4 + 3 ≤ header + 16 + 2 * (q + 2) by omega).trans_lt hroom)
    ?_ hframe
  dsimp only [header, bits, capWords, PSTRQueryLayout.header, PSTRQueryLayout.parentsBase,
    PSTRQueryLayout.countsBase, PSTRQueryLayout.physicalWorkspace,
    PSTRStaticHeap.metadataAddress, physicalHeaderWords]
  omega

end PaperProofs.Structure.LaminarTree.PA17A19QueryBridgeRankFrame012
