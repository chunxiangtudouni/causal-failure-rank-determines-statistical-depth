module

public import PaperProofs.Structure.PSTR_CountedOutside_080
public import PaperProofs.Structure.PSTR_AdvanceOutside_081

/-! One original outer iteration, with its true next Ready and persistent
heap/heads-suffix frame at EVERY clock of the SAME execution witness. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRIterationOutside

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRQueryLayout PSTRCountWorkspace

theorem actual_step {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (state : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (ready : PSTRCountReady.Ready full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node.val state) :
    ∃ steps ≤ 387 + 114 * ((prepareNormalization q full).indexed.children.get node).size,
      PSTRCountReady.Ready full configuration origin
        (capacityWords 8192 full.length q (treeSize q full)) (node.val + 1)
        (packingRun (callInput q full command) whole steps state) ∧
      (∀ clock ≤ steps,
        let result := packingRun (callInput q full command) whole clock state
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
        ∀ physical, Fits (indexWidth 32 full.length q) physical →
          (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) =
            state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) := by
  obtain ⟨steps, hsteps, counted, prefixes⟩ := PSTRCountedOutside.actual_counted full command configuration origin node
    state whole hc hwords hpcfit hq hl ready
  have next := PSTRCountAdvanceStep.actual_advance full command configuration origin node state
    (packingRun (callInput q full command) whole steps state) whole hc hwords hpcfit hq hl ready counted
  refine ⟨steps + 85, by omega, ?_, ?_⟩
  · rw [PSTRWordSegments.run_add]
    exact next
  · intro clock hclock
    by_cases hfirst : clock ≤ steps
    · exact prefixes clock hfirst
    · rw [show clock = steps + (clock - steps) by omega, PSTRWordSegments.run_add]
      have tail := PSTRAdvanceOutside.actual_prefix full command configuration origin node state
        (packingRun (callInput q full command) whole steps state) whole hc hwords hpcfit hq hl counted
        (clock - steps) (by omega)
      refine ⟨tail.1, ?_⟩
      intro physical hp hh
      exact (tail.2 physical hp hh).trans ((prefixes steps le_rfl).2 physical hp hh)

end PaperProofs.Structure.LaminarTree.PSTRIterationOutside
