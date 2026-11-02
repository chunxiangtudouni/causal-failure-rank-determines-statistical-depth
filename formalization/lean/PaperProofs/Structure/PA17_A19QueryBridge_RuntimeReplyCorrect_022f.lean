module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022e
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReplyCorrect_022b

/-! The real selector reads each payload word from the same-call logical
snapshot. A nonzero H7 proves the selected entry is a vector; its existing
table representation then identifies that payload, without a tag getter. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments

def payloadCapacity {q : Nat} (cache : IndexedNodeCache (Fin q))
    (scalarHeap : Nat → Nat) (payloadBase : Nat) : IndexedCapacity cache :=
  Vector.ofFn (fun target => scalarHeap (payloadBase + target.val))

theorem payloadCapacity_get {q : Nat} (cache : IndexedNodeCache (Fin q))
    (scalarHeap : Nat → Nat) (payloadBase : Nat) (target : cache.NodeId) :
    (payloadCapacity cache scalarHeap payloadBase).get target = scalarHeap (payloadBase + target.val) := by
  exact cache_get_ofFn _ target

theorem payload_eq_of_vector_rep {q : Nat} (cache : IndexedNodeCache (Fin q))
    (scalarHeap : Nat → Nat) (entryBase : Nat) (payload capacity : IndexedCapacity cache)
    (hpayload : ∀ target : cache.NodeId, scalarHeap (entryBase + 1 + target.val) = payload.get target)
    (hentry : PA17TagBridge001.TagFirstRep cache scalarHeap entryBase (.vector capacity)) :
    payload = capacity := by
  apply Vector.ext
  intro index hi
  change payload.get ⟨index, hi⟩ = capacity.get ⟨index, hi⟩
  rw [← hpayload ⟨index, hi⟩, hentry.2 ⟨index, hi⟩]

theorem payloadCapacity_eq_of_vector_rep {q : Nat} (cache : IndexedNodeCache (Fin q))
    (scalarHeap : Nat → Nat) (entryBase : Nat) (capacity : IndexedCapacity cache)
    (hentry : PA17TagBridge001.TagFirstRep cache scalarHeap entryBase (.vector capacity)) :
    payloadCapacity cache scalarHeap (entryBase + 1) = capacity := by
  apply payload_eq_of_vector_rep cache scalarHeap entryBase _ capacity
  · intro target
    exact (payloadCapacity_get cache scalarHeap (entryBase + 1) target).symm
  · exact hentry

theorem inputs_selected_entry_rep {q : Nat} (cache : IndexedNodeCache (Fin q))
    (rowPointer countsBase parentBase nodePointer rowBase : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1))
    (node : Option cache.NodeId) (scalarHeap : Nat → Nat)
    (hi : PA17QueryTests009.Inputs cache rowPointer countsBase parentBase nodePointer rowBase counts row node scalarHeap) :
    PA17TagBridge001.TagFirstRep cache scalarHeap
      (rowBase + (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) * (cache.nodes.size + 1))
      (IndexedQuery.entryAt row (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)) := by
  have hbound := PA17QueryRanks011.firstFalseValue_le q (IndexedQuery.budgetExtensionTest cache counts row node)
  have hprev : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1 < q + 2 := by omega
  rw [IndexedQuery.entryAt_get row _ hprev]
  exact hi.entries ⟨_, hprev⟩

theorem enabled_raw_slot_canonical {bits q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts : IndexedCapacity cache)
    (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (scalarHeap : Nat → Nat) (entryBase : Nat) (payload : IndexedCapacity cache)
    (active header toolSlot : Nat) (state : WordState bits)
    (hpayload : ∀ target : cache.NodeId, scalarHeap (entryBase + 1 + target.val) = payload.get target)
    (hentry : PA17TagBridge001.TagFirstRep cache scalarHeap entryBase
      (IndexedQuery.entryAt row (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)))
    (hflag : state.heap (BitVec.ofNat bits (header + 7)) = BitVec.ofNat bits
      (if active = 0 then 0 else if PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) = 0 then 0 else 1))
    (hslot : state.heap (BitVec.ofNat bits toolSlot) = BitVec.ofNat bits
      (PA17LeafLabels005.encodeTool (node.bind (IndexedDescent.selectAt cache leaves counts payload)))) :
    (state.heap (BitVec.ofNat bits (header + 7))).toNat ≠ 0 →
      state.heap (BitVec.ofNat bits toolSlot) = BitVec.ofNat bits
        (PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node
          (IndexedQuery.entryAt row (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1)))) := by
  intro henabled
  have hb : PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) ≠ 0 := by
    intro hz
    have hzero : state.heap (BitVec.ofNat bits (header + 7)) = BitVec.ofNat bits 0 := by
      simpa only [hz, ite_true, ite_self] using hflag
    apply henabled
    rw [hzero]
    rfl
  have hp : ∀ capacity : IndexedCapacity cache,
      IndexedQuery.entryAt row
        (PA17QueryRanks011.firstFalseValue q (IndexedQuery.budgetExtensionTest cache counts row node) - 1) = .vector capacity →
      payload = capacity := by
    intro capacity hc
    rw [hc] at hentry
    exact payload_eq_of_vector_rep cache scalarHeap entryBase payload capacity hpayload hentry
  rw [hslot, raw_payload_encodeTool_eq cache leaves counts row node payload hb hp]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeReplyCorrect022
