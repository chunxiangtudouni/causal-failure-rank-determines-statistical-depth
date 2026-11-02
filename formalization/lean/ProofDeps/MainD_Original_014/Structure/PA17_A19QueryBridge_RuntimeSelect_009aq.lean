module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009an

/-! Full actual parent kernel's candidate, tied to its original entry heap.
The executed clear and initialization establish zero candidates; actual
prefix frames preserve every materialized source and original packed scalar. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem actual_parent_capacity_frame {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (clock : Nat) (hc : clock ≤ parentSteps size) (address : Nat) (ha : address < capWords) :
    logicalHeap q capWords (packingRun (callInput q full command) containing clock state).heap address =
      logicalHeap q capWords state.heap address := by
  apply PSTRRepairHeap.logical_frame state.heap _ capWords 0 (header + 8) address
    (by have hb := layout.bits8; omega) layout.positive layout.capacityFits
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide))
    (by have hm := layout.metadata_le; omega) ?_ (by omega)
  intro physical hphysical
  exact actual_parent_frame em layout command configuration state data clock hc physical
    ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits) (.inl hphysical)

theorem actual_parent_candidate_find {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (target : Nat) (htarget : 0 < target) (htargetBound : target ≤ size) :
    (packingRun (callInput q full command) containing (parentSteps size) state).heap
        (BitVec.ofNat bits (childBase header q + target)) =
      BitVec.ofNat bits (childSuffix size 0 (parentHit q capWords base counts parents target state.heap)) := by
  let rom := callInput q full command
  let prepared := packingRun rom containing (clearSteps size + 38) state
  have hi := data.initial_ready em layout command configuration state
  have hc : clearSteps size + 38 ≤ parentSteps size := by unfold parentSteps; omega
  have hsame (node : Nat) (hn : node < size) :
      parentHit q capWords base counts parents target prepared.heap node =
        parentHit q capWords base counts parents target state.heap node := by
    have hp := actual_parent_frame em layout command configuration state data (clearSteps size + 38) hc
      (parents + (node + 1)) ((show parents + (node + 1) ≤ header + 8 by have hh := layout.parentsEnd; omega).trans_lt (layout.headerFits 8 (by decide)))
      (.inl (by have hh := layout.parentsEnd; omega))
    have hcount := actual_parent_frame em layout command configuration state data (clearSteps size + 38) hc
      (counts + node) ((show counts + node ≤ header + 8 by have hh := layout.countsEnd; omega).trans_lt (layout.headerFits 8 (by decide)))
      (.inl (by have hh := layout.countsEnd; omega))
    have hcap := actual_parent_capacity_frame em layout command configuration state data (clearSteps size + 38) hc
      (base + node) (by have hh := layout.payloadBound; omega)
    dsimp only [parentHit, prepared, rom]
    rw [hp, hcount, hcap]
  have he : (List.range' 0 (size - 0)).find? (parentHit q capWords base counts parents target prepared.heap) =
      (List.range' 0 (size - 0)).find? (parentHit q capWords base counts parents target state.heap) := by
    apply List.find?_congr
    intro node hn
    have hmem := List.mem_range'.mp hn
    obtain ⟨index, hind, heq⟩ := hmem
    apply hsame node
    omega
  rw [parentSteps, run_add, actual_reverse_candidate (parent_reverse_embedded em) layout command configuration prepared hi.1
    target htarget htargetBound (hi.2 target (by omega))]
  simp only [childSuffix, he]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
