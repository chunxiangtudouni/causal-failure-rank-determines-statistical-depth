module

public import PaperProofs.Structure.PSTR_CountBootstrap_040
public import PaperProofs.Structure.PSTR_CountLogical_055
public import PaperProofs.Structure.PA17_A19QueryBridge_Numeric_006b

/-! Original word/allocation instances for the actual positive-q bootstrap.
Reuse the frozen A17 numeric cone. No frozen16-bit wrapper is renamed: the
already-proved generic Word bootstrap itself is instantiated at word32.
RF and IF remain universally fixed implementation constants in [64,65536]
where needed; the common8192 candidate is an ordinary instance of these. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROriginalCountRoom

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRQueryLayout

theorem word_lower (N q : Nat) : 32 ≤ indexWidth 32 N q := by
  have hc : 0 < Nat.clog 2 (N + q + 2) := Nat.clog_pos (by decide) (by omega)
  unfold indexWidth
  omega

theorem quadratic_room (N q value : Nat) (hv : value ≤ (N + q + 2) ^ 2 + 1024) :
    Fits (indexWidth 32 N q) value := by
  have h16 : Fits (indexWidth 16 N q) value := fits_indexWidth_of_lt_power 16 N q value
    (hv.trans_lt (quadratic_add_lt_power16 (N + q + 2) (by omega)))
  exact PA17WordBounds023.fits_mono_bits (PA17WordBounds023.indexWidth_mono_factor 16 32 N q (by decide)) h16

theorem raw_rooms (N q : Nat) :
    Fits (indexWidth 32 N q) N ∧ Fits (indexWidth 32 N q) (2 + N * q) ∧
      Fits (indexWidth 32 N q) (2 * (q + 1)) := by
  have hd : 2 * (N + q + 2) ≤ (N + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right (N + q + 2) (show 2 ≤ N + q + 2 by omega)
  have hm : N * q ≤ (N + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show N ≤ N + q + 2 by omega) (show q ≤ N + q + 2 by omega)
  exact ⟨quadratic_room N q N (by omega),
    quadratic_room N q (2 + N * q) (by omega),
    quadratic_room N q (2 * (q + 1)) (by omega)⟩

theorem dimension_rooms {q : Nat} (full : List (Finset (Fin q))) :
    Fits (indexWidth 32 full.length q) (full.length + 1) ∧
      Fits (indexWidth 32 full.length q) (q + 2) ∧
      Fits (indexWidth 32 full.length q) ((prepareNormalization q full).indexed.nodes.size + 1) ∧
      Fits (indexWidth 32 full.length q) ((full.length + 1) * (q + 2)) ∧
      Fits (indexWidth 32 full.length q) q := by
  have ht := prepared_indexed_size_le q full
  have hd : full.length + q + 2 ≤ (full.length + q + 2) ^ 2 := by
    have hp := Nat.pow_le_pow_right (show 1 ≤ full.length + q + 2 by omega) (show 1 ≤ 2 by decide)
    simpa only [pow_one] using hp
  have hm : (full.length + 1) * (q + 2) ≤ (full.length + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (show full.length + 1 ≤ full.length + q + 2 by omega)
      (show q + 2 ≤ full.length + q + 2 by omega)
  exact ⟨quadratic_room full.length q _ (by omega),
    quadratic_room full.length q _ (by omega), quadratic_room full.length q _ (by omega),
    quadratic_room full.length q _ (by omega), quadratic_room full.length q _ (by omega)⟩

theorem workspace_rooms {q : Nat} (full : List (Finset (Fin q)))
    (scratchFactor indexFactor : Nat) (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536)
    (h64 : 64 ≤ indexFactor) (hq : 0 < q) (hl : LaminarSchedule full) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    let workspace := PSTRCountWorkspace.base q full capWords bits
    Fits bits (workspace + 15) ∧
      Fits bits (parentsBase workspace (prepareNormalization q full).indexed.nodes.size +
        (prepareNormalization q full).indexed.nodes.size) := by
  dsimp only
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords scratchFactor full.length q (treeSize q full)
  let workspace := PSTRCountWorkspace.base q full capWords bits
  have he := endpoint_index_factor full capWords bits indexFactor hq hl h64
  rw [PSTRCountLogical.workspace_eq full capWords bits hq] at he
  have hh := PA17A19QueryBridgeNumeric006b.heap_room full scratchFactor indexFactor hs hi
  have hend : Fits bits (endpoint workspace (treeSize q full) q) := he.trans_lt hh
  have ht : treeSize q full = (prepareNormalization q full).indexed.nodes.size := by
    simp only [treeSize, ne_of_gt hq, ite_false]
  rw [endpoint_eq, ht] at hend
  constructor
  · exact (show workspace + 15 ≤ workspace + 3 * (prepareNormalization q full).indexed.nodes.size + 2 * q + 40 by omega).trans_lt hend
  · exact (show parentsBase workspace (prepareNormalization q full).indexed.nodes.size +
      (prepareNormalization q full).indexed.nodes.size ≤ workspace + 3 * (prepareNormalization q full).indexed.nodes.size + 2 * q + 40 by
        unfold parentsBase countsBase; omega).trans_lt hend

theorem bitmap_room {q : Nat} (full : List (Finset (Fin q))) (scratchFactor : Nat) (hq : 0 < q) :
    tableWords full.length q (treeSize q full) + q ≤
      capacityWords scratchFactor full.length q (treeSize q full) := by
  simp only [capacityWords, ne_of_gt hq, ite_false]
  omega

theorem actual_bootstrap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (scratchFactor indexFactor : Nat)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords scratchFactor full.length q (treeSize q full)) configuration heap) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords scratchFactor full.length q (treeSize q full)
    let workspace := PSTRCountWorkspace.base q full capWords bits
    let after := packingRun (callInput q full command) PSTRCountBootstrapCode.program
      (8 * CapacityBits.width q + 56) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 305 ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧
      after.register .index = BitVec.ofNat bits 0 ∧ after.register .fresh = BitVec.ofNat bits 0 ∧
      after.register .value = BitVec.ofNat bits 0 ∧
      (∀ offset < 4, after.heap (BitVec.ofNat bits (workspace + 12 + offset)) =
        if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
        else if offset = 1 then AlgorithmClaims.PackedCapacityRAM.lowMask bits (CapacityBits.width q)
        else BitVec.ofNat bits 0) ∧
      (∀ address < workspace + 12, after.heap (BitVec.ofNat bits address) = heap (BitVec.ofNat bits address)) := by
  have raw := raw_rooms full.length q
  have wr := workspace_rooms full scratchFactor indexFactor hs hi h64 hq hl
  exact PSTRCountBootstrap.actual_bootstrap full command configuration _ heap
    (by have h := word_lower full.length q; omega) hq rep raw.1 raw.2.1 raw.2.2 wr.1

theorem bootstrap_rep {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (scratchFactor indexFactor : Nat)
    (hs : scratchFactor ≤ 65536) (hi : indexFactor ≤ 65536) (h64 : 64 ≤ indexFactor)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords scratchFactor full.length q (treeSize q full)) configuration heap) :
    HeapRepresents q full (capacityWords scratchFactor full.length q (treeSize q full)) configuration
      (packingRun (callInput q full command) PSTRCountBootstrapCode.program
        (8 * CapacityBits.width q + 56) (packingInitial heap)).heap := by
  have raw := raw_rooms full.length q
  have wr := workspace_rooms full scratchFactor indexFactor hs hi h64 hq hl
  exact PSTRCountBootstrap.heap_represents full command configuration _ heap
    (by have h := word_lower full.length q; omega) hq rep raw.1 raw.2.1 raw.2.2 wr.1
    (bitmap_room full scratchFactor hq) (PA17A19QueryBridgeNumeric006b.scalar_room full scratchFactor hs)

end PaperProofs.Structure.LaminarTree.PSTROriginalCountRoom
