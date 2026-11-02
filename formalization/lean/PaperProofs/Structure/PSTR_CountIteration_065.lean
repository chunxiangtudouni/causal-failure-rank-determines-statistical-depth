module

public import PaperProofs.Structure.PSTR_CountAdvanceStep_064

/-! One real outer iteration and its repeated genuine execution. The
weighted clock invariant telescopes the actual flat-child degree offsets,
retaining the SAME evolving WordState throughout every iteration. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountIteration

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

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
        (packingRun (callInput q full command) whole steps state) := by
  obtain ⟨steps, hsteps, counted⟩ := PSTRNodeCounted.actual_counted full command configuration origin node
    state whole hc hwords hpcfit hq hl ready
  have next := PSTRCountAdvanceStep.actual_advance full command configuration origin node state
    (packingRun (callInput q full command) whole steps state) whole hc hwords hpcfit hq hl ready counted
  refine ⟨steps + 85, by omega, ?_⟩
  rw [PSTRWordSegments.run_add]
  exact next

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
          (packingRun (callInput q full command) whole steps state) := by
  induction count with
  | zero =>
    intro node state _ ready
    exact ⟨0, by simp, by simpa only [Nat.add_zero, packingRun] using ready⟩
  | succ count ih =>
    intro node state hbound ready
    have hnode : node < (prepareNormalization q full).indexed.nodes.size := by omega
    let current : (prepareNormalization q full).indexed.NodeId := ⟨node, hnode⟩
    obtain ⟨first, hfirst, next⟩ := actual_step full command configuration origin current state whole hc hwords hpcfit hq hl ready
    obtain ⟨later, hlater, last⟩ := ih (node + 1) (packingRun (callInput q full command) whole first state) (by omega) next
    have hoff := PSTRCountChildRows.offset_succ full current
    change PSTRCountChildRows.flatOffset full (node + 1) = PSTRCountChildRows.flatOffset full node +
      ((prepareNormalization q full).indexed.children.get current).size at hoff
    have he : node + 1 + count = node + (count + 1) := by omega
    rw [he] at hlater last
    rw [hoff] at hlater
    refine ⟨first + later, by omega, ?_⟩
    rw [PSTRWordSegments.run_add]
    exact last

end PaperProofs.Structure.LaminarTree.PSTRCountIteration
