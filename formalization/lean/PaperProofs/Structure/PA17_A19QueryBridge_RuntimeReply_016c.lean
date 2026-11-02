module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReply_016b
public import PaperProofs.Structure.PA17_A19QueryBridge_Numeric_006b

/-! Original A19 allocation and word-factor instantiation. The only live
entry facts concern actual fields materialized by this same query call. -/

@[expose] public section
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem literal_words_fit {bits : Nat} (hb : 8 ≤ bits) :
    WordsFit bits (packingCode program) := by
  have bound : ∀ word ∈ packingCode program, word ≤ 255 := by decide
  have power : 256 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb
  intro word hw
  exact lt_of_le_of_lt (bound word hw) (by omega)

theorem code_length : (packingCode program).length = 165 := rfl

theorem original_room {q : Nat} (full : List (Finset (Fin q)))
    (scratchFactor indexFactor : Nat)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    let endpoint := PSTRQueryLayout.endpoint
      (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full) q
    let heapWords := physicalHeaderWords + packedCapacityWords q capWords bits +
      indexFactor * (full.length + q + treeSize q full + 1)
    Fits bits endpoint ∧ endpoint ≤ heapWords := by
  dsimp only
  have allocation := PSTRQueryLayout.endpoint_index_factor full
    (capacityWords scratchFactor full.length q (treeSize q full))
    (indexWidth 32 full.length q) indexFactor hq hl h64
  exact ⟨allocation.trans_lt (PA17A19QueryBridgeNumeric006b.heap_room full scratchFactor indexFactor hs hi),
    allocation⟩

theorem original_prefix_decoded {q origin : Nat} (full : List (Finset (Fin q)))
    (command : Command) (configuration : Configuration q) (scratchFactor indexFactor : Nat)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full) (containing : List PackingOp)
    (em : Embedded (indexWidth 32 full.length q) origin containing)
    (state : WordState (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords scratchFactor full.length q (treeSize q full)) configuration state.heap)
    (hh : state.register .address = BitVec.ofNat _
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full
        (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q)) (treeSize q full)))
    (hp : state.pc = BitVec.ofNat _ (5 * origin)) (ha : state.halted = false)
    (count : Nat) (hc : count < 32) :
    let heapWords := physicalHeaderWords + packedCapacityWords q
      (capacityWords scratchFactor full.length q (treeSize q full)) (indexWidth 32 full.length q) +
        indexFactor * (full.length + q + treeSize q full + 1)
    let before := packingRun (callInput q full command) containing count state
    before.halted = false ∧ Fits (indexWidth 32 full.length q) (before.pc.toNat + 4) ∧
      before.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ op, PackingOp.decode (physicalFetch (indexWidth 32 full.length q) (packingCode containing) before.pc.toNat) = some op ∧
        packingAccessFits (callInput q full command) heapWords before op := by
  have room := original_room full scratchFactor indexFactor hs hi h64 hq hl
  exact actual_prefix_decoded em (callInput q full command) _ _ q _ state room.1 room.2
    (by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM])
    (by simp [callInput, RawTreePreprocessingClaims.rawIncidenceROM, PhysicalROM.words]) rep.1 hh hp ha count hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReply016
