module

public import Structure.PSTR_UniformBootstrapOutside_117
public import Structure.PSTR_UniformCountReady_108
public import Structure.PSTR_CountCompleteOutside_085

/-! NEW bootstrap/sentinel trueReady63, original representation and FULL
low-or-high physical frame at EVERY real prefix, same original raw run. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformReadyOutside
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

theorem ready_zero_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget) (co : PSTROuterCountCode.Contains whole 63)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap) :
    PSTRCountReady.Ready full configuration 63 (capacityWords 8192 full.length q (treeSize q full)) 0
      (packingRun (callInput q full command) whole (8 * CapacityBits.width q + 63) state) ∧
    (∀ clock ≤ 8 * CapacityBits.width q + 63,
      let result := packingRun (callInput q full command) whole clock state
      HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
      ∀ physical, Fits (indexWidth 32 full.length q) physical →
        (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
        result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 58) state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have bootPrefixes (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 58) :=
    PSTRUniformBootstrapOutside.actual_prefix full command configuration whole zeroTarget cb hwords hpcfit hq hl
      state hp ha rep clock hc
  have data := PSTRUniformPositiveBootstrap.actual_bootstrap full command configuration whole zeroTarget cb hwords hpcfit
    state hp ha hq hl rep
  have boot_rep : HeapRepresents q full capWords configuration boot.heap := (bootPrefixes _ le_rfl).1
  have hbase : boot.register .old = BitVec.ofNat bits (countsBase workspace) := data.2.2.1
  have ht : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using
      (PSTRStaticHeap.headers full configuration capWords boot.heap boot_rep).1
  have hroom : Fits bits (parentsBase workspace size) := (Nat.le_add_right _ size).trans_lt rooms.2
  have hpRoom : Fits bits (parentsBase workspace (treeSize q full)) := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using hroom
  have hs := PSTROuterCountCode.sentinel_at whole 63 co
  have high_base (physical : Nat) (hh : physical < workspace ∨ endpoint workspace size q ≤ physical) :
      physical < workspace ∨ workspace + 16 ≤ physical := by
    rcases hh with low | high
    · exact Or.inl low
    · right
      rw [endpoint_eq] at high
      omega
  refine ⟨PSTRUniformCountReady.actual_ready_zero full command configuration whole zeroTarget cb co hwords hpcfit hq hl state hp ha rep, ?_⟩
  intro clock hclock
  dsimp only
  by_cases hboot : clock ≤ 8 * CapacityBits.width q + 58
  · have hp := bootPrefixes clock hboot
    exact ⟨hp.1, fun physical hf hh => hp.2 physical hf (high_base physical hh)⟩
  · rw [show clock = (8 * CapacityBits.width q + 58) + (clock - (8 * CapacityBits.width q + 58)) by omega,
      PSTRWordSegments.run_add,
      PSTRWidthPrefix.straight_prefix rom whole PSTRParentSentinel.program 63 hs.bound hs.code
        PSTRParentSentinel.program_straight hwords hpcfit boot data.2.1 data.1
        (clock - (8 * CapacityBits.width q + 58)) (by rw [PSTRParentSentinel.program_length]; omega)]
    refine ⟨PSTROuterMemory.sentinel_prefix_rep full rom configuration capWords boot (by omega) hq boot_rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hpRoom hbase
      (clock - (8 * CapacityBits.width q + 58)) (by omega), ?_⟩
    intro physical hf hh
    have different : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (parentsBase workspace size) := by
      apply (ofNat_injective_of_fit _ _ hf hroom).not.mpr
      change physical < workspace ∨ endpoint workspace size q ≤ physical at hh
      rcases hh with low | high
      · change physical ≠ workspace + 16 + size
        omega
      · rw [endpoint_eq] at high
        change physical ≠ workspace + 16 + size
        omega
    exact (PSTROuterStoreFrame.sentinel_prefix_outside rom workspace size boot hbase ht _ different
      (clock - (8 * CapacityBits.width q + 58)) (by omega)).trans
        ((bootPrefixes (8 * CapacityBits.width q + 58) le_rfl).2 physical hf (high_base physical hh))

end PaperProofs.Structure.LaminarTree.PSTRUniformReadyOutside
