module

public import Structure.PSTR_UniformCountSafe_119
public import Structure.PSTR_ArbitraryOutside_086

/-! NEW arbitrary-register original guarded count producer. ONE real run
has original counts/parents, exact table inclVOID, all capacity bounds,
full low/high frames and actual access safety at EVERY relevant clock. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformCountProducer

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace PSTRArbitraryOutside

theorem actual_complete {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget) (co : PSTROuterCountCode.Contains whole 63)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false) :
    ∃ steps, 68 ≤ steps ∧
      steps ≤ 8 * CapacityBits.width q + 68 + 501 * (prepareNormalization q full).indexed.nodes.size ∧
      PSTRCountComplete.Complete full configuration 63 (capacityWords 8192 full.length q (treeSize q full))
        (packingRun (callInput q full command) whole steps state) ∧
      (∀ clock ≤ steps,
        let result := packingRun (callInput q full command) whole clock state
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
        ∀ physical, Fits (indexWidth 32 full.length q) physical →
          (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) ∧
      (∀ clock ≤ steps, CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
        (logicalHeap q (capacityWords 8192 full.length q (treeSize q full))
          (packingRun (callInput q full command) whole clock state).heap)) ∧
      (∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q (capacityWords 8192 full.length q (treeSize q full))
          (packingRun (callInput q full command) whole clock state).heap address =
        logicalHeap q (capacityWords 8192 full.length q (treeSize q full)) state.heap address) ∧
      (∀ clock < steps, PSTRCountKernel.AtSafe (callInput q full command) whole
        (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
          (prepareNormalization q full).indexed.nodes.size q)
        (packingRun (callInput q full command) whole clock state)) := by
  let rom := callInput q full command
  obtain ⟨steps, lower, upper, complete, prefixes, fetches⟩ := PSTRUniformCountSafe.actual_complete
    full command configuration whole zeroTarget cb co hwords hpcfit hq hl state hp ha rep
  refine ⟨steps, lower, upper, complete, prefixes, ?_, ?_, fetches⟩
  · intro clock hclock
    exact represents_capacity full configuration _ _ hq (prefixes clock hclock).1
  · intro clock hclock address ha
    have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
    have bitmap := PSTROriginalCountRoom.bitmap_room full 8192 hq
    apply persistent_logical_frame full state.heap (packingRun rom whole clock state).heap hq hl ?_ address (by omega)
    intro physical hphysical
    have hp : Fits (indexWidth 32 full.length q) physical :=
      hphysical.trans ((Nat.le_add_right _ 15).trans_lt rooms.1)
    exact (prefixes clock hclock).2 physical hp (Or.inl hphysical)

end PaperProofs.Structure.LaminarTree.PSTRUniformCountProducer
