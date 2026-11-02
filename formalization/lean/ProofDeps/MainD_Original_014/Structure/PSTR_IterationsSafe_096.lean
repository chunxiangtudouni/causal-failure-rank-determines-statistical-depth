module

public import Structure.PSTR_IterationSafe_095

/-! Genuine weighted iteration induction with cumulative EVERYclock heap
representation and endpoint suffix frame. The internal Ready premise is
derived by the real raw bootstrap, not added to original callers. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRIterationsSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRQueryLayout PSTRCountWorkspace

theorem actual_iterations {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (whole : List PackingOp) (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full) (count : Nat) :
    ∀ (node : Nat) (state : WordState (indexWidth 32 full.length q)),
      node + count ≤ (prepareNormalization q full).indexed.nodes.size →
      PSTRCountReady.Ready full configuration origin
        (capacityWords 8192 full.length q (treeSize q full)) node state →
      ∃ steps,
        steps + 114 * PSTRCountChildRows.flatOffset full node ≤
          387 * count + 114 * PSTRCountChildRows.flatOffset full (node + count) ∧
        PSTRCountReady.Ready full configuration origin
          (capacityWords 8192 full.length q (treeSize q full)) (node + count)
          (packingRun (callInput q full command) whole steps state) ∧
        (∀ clock ≤ steps,
          let result := packingRun (callInput q full command) whole clock state
          HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
          ∀ physical, Fits (indexWidth 32 full.length q) physical →
            (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
              (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
              (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
            result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) =
              state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) ∧
      (∀ clock < steps, PSTRCountKernel.AtSafe (callInput q full command) whole
        (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
          (prepareNormalization q full).indexed.nodes.size q)
        (packingRun (callInput q full command) whole clock state)) := by
  induction count with
  | zero =>
    intro node state _ ready
    refine ⟨0, by simp, ?_, ?_, ?_⟩
    · simpa only [Nat.add_zero, packingRun] using ready
    · intro clock hclock
      have hz : clock = 0 := by omega
      subst clock
      exact ⟨ready.rep, fun _ _ _ => rfl⟩
    · intro clock hclock
      omega
  | succ count ih =>
    intro node state hbound ready
    have hnode : node < (prepareNormalization q full).indexed.nodes.size := by omega
    let current : (prepareNormalization q full).indexed.NodeId := ⟨node, hnode⟩
    obtain ⟨first, hfirst, next, firstPrefixes, firstFetch⟩ := PSTRIterationSafe.actual_step full command configuration origin current state
      whole hc hwords hpcfit hq hl ready
    obtain ⟨later, hlater, last, laterPrefixes, laterFetch⟩ := ih (node + 1)
      (packingRun (callInput q full command) whole first state) (by omega) next
    have hoff := PSTRCountChildRows.offset_succ full current
    change PSTRCountChildRows.flatOffset full (node + 1) = PSTRCountChildRows.flatOffset full node +
      ((prepareNormalization q full).indexed.children.get current).size at hoff
    have he : node + 1 + count = node + (count + 1) := by omega
    rw [he] at hlater last
    rw [hoff] at hlater
    refine ⟨first + later, by omega, ?_, ?_, ?_⟩
    · rw [PSTRWordSegments.run_add]
      exact last
    · intro clock hclock
      by_cases hfirstClock : clock ≤ first
      · exact firstPrefixes clock hfirstClock
      · rw [show clock = first + (clock - first) by omega, PSTRWordSegments.run_add]
        have after := laterPrefixes (clock - first) (by omega)
        refine ⟨after.1, ?_⟩
        intro physical hp hh
        exact (after.2 physical hp hh).trans ((firstPrefixes first le_rfl).2 physical hp hh)

    · intro clock hclock
      by_cases hfirstClock : clock < first
      · exact firstFetch clock hfirstClock
      · rw [show clock = first + (clock - first) by omega, PSTRWordSegments.run_add]
        exact laterFetch (clock - first) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRIterationsSafe
