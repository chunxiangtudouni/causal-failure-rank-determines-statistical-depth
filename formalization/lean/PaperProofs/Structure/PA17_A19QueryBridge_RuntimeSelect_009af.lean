module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ae

/-! The real parent kernel establishes every candidate word <=t, including
sentinel0. This is a local scratch invariant derived from actual clearing
and pushes; arbitrary original VOID payloads need only their original q bound. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def CandidateBounded {bits : Nat} (header q size : Nat) (heap : BitVec bits → BitVec bits) : Prop :=
  heap (BitVec.ofNat bits (childBase header q)) = BitVec.ofNat bits 0 ∧
    ∀ encoded ≤ size, (heap (BitVec.ofNat bits (childBase header q + encoded))).toNat ≤ size

theorem reverseReady_heap {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state) :
    let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
    let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
    let cap := logicalHeap q capWords state.heap (base + remaining)
    (packingRun (callInput q full command) containing 105 state).heap = reverseStepHeap header (childBase header q) parent remaining
      (pushedValue remaining parent cap count (state.heap (BitVec.ofNat bits (childBase header q + parent)))) state.heap := by
  let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
  let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
  have hrem : remaining < size := by have hh := ready.bound; omega
  have hparent : parent ≤ size := ready.data.parentBound remaining hrem
  have hparentWord : state.heap (BitVec.ofNat bits (parents + (remaining + 1))) = BitVec.ofNat bits parent := by
    simp only [parent, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcountWord : state.heap (BitVec.ofNat bits (counts + remaining)) = BitVec.ofNat bits count := by
    simp only [count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hr := actual_reverse_push em full command configuration capWords heapWords header base (childBase header q)
    counts parents remaining parent count state layout.bits8 layout.positive layout.width ready.data.represents
    layout.capacityFits layout.heapFits layout.header_eq (by have hh := layout.headerAllocated; omega)
    ready.data.width ready.data.mask layout.oneFits (ready.bound.trans_lt layout.sizeFits) (BitVec.isLt _) (BitVec.isLt _)
    ((show base + remaining ≤ base + size by omega).trans_lt layout.payloadFits)
    (by have hh := layout.payloadBound; omega) (by unfold childBase; omega) (layout.targetFits parent hparent)
    ready.address ready.pc ready.active ready.counter ready.data.payload ready.data.candidates
    ready.data.countsBase ready.data.parentsBase hcountWord hparentWord
  exact hr.2.2.2.2.2

theorem reverseReady_candidateBounded {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (bounded : CandidateBounded header q size state.heap) :
    CandidateBounded header q size (packingRun (callInput q full command) containing 105 state).heap := by
  let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
  let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
  let cap := logicalHeap q capWords state.heap (base + remaining)
  let selected := pushedValue remaining parent cap count (state.heap (BitVec.ofNat bits (childBase header q + parent)))
  have hp : parent ≤ size := ready.data.parentBound remaining (by have hh := ready.bound; omega)
  have hm := reverseReady_heap em layout command configuration state ready
  have hn (encoded : Nat) (he : encoded ≤ size) :
      BitVec.ofNat bits (childBase header q + encoded) ≠ BitVec.ofNat bits (header + 8) := by
    apply (ofNat_injective_of_fit _ _
      ((Nat.le_succ _).trans_lt (layout.targetFits encoded he)) (layout.headerFits 8 (by decide))).not.mpr
    unfold childBase
    omega
  have hu (encoded : Nat) (he : encoded ≤ size) (hne : encoded ≠ parent) :
      BitVec.ofNat bits (childBase header q + encoded) ≠ BitVec.ofNat bits (childBase header q + parent) := by
    apply (ofNat_injective_of_fit _ _ ((Nat.le_succ _).trans_lt (layout.targetFits encoded he))
      ((Nat.le_succ _).trans_lt (layout.targetFits parent hp))).not.mpr
    omega
  constructor
  · rw [hm, reverseStepHeap, Function.update_of_ne (by simpa only [Nat.add_zero] using hn 0 (by omega))]
    by_cases hz : parent = 0
    · change Function.update state.heap (BitVec.ofNat bits (childBase header q + parent)) selected (BitVec.ofNat bits (childBase header q)) = BitVec.ofNat bits 0
      simp only [hz, Nat.add_zero, selected, pushedValue, ite_true, Function.update_self]
      exact bounded.1
    · rw [Function.update_of_ne (by simpa only [Nat.add_zero] using hu 0 (by omega) (by omega))]
      exact bounded.1
  · intro encoded he
    rw [hm, reverseStepHeap, Function.update_of_ne (hn encoded he)]
    by_cases hz : encoded = parent
    · subst encoded
      rw [Function.update_self]
      exact pushedValue_toNat_le remaining parent cap count _ size ready.bound (bounded.2 parent hp)
    · rw [Function.update_of_ne (hu encoded he hz)]
      exact bounded.2 encoded he

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
