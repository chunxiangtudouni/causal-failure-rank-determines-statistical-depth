module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009ag

/-! Canonical-parent scan's mathematical suffix and actual point update.
The Boolean condition is defined from the SAME run's actual parent/count
words and original packed scalar, not supplied as an answer or a trace. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def childSuffix (size remaining : Nat) (test : Nat → Bool) : Nat :=
  (((List.range' remaining (size - remaining)).find? test).map Nat.succ).getD 0

theorem childSuffix_init (size : Nat) (test : Nat → Bool) : childSuffix size size test = 0 := by simp [childSuffix]

theorem childSuffix_step (size remaining : Nat) (test : Nat → Bool) (hr : remaining < size) :
    childSuffix size remaining test = if test remaining then remaining + 1 else childSuffix size (remaining + 1) test := by
  have he : size - remaining = (size - (remaining + 1)) + 1 := by omega
  unfold childSuffix
  rw [he, List.range'_succ]
  cases ht : test remaining <;> simp [ht]

theorem childSuffix_bound (size remaining : Nat) (test : Nat → Bool) : childSuffix size remaining test ≤ size := by
  unfold childSuffix
  cases hh : (List.range' remaining (size - remaining)).find? test with
  | none => simp
  | some value =>
    have hm := List.mem_of_find?_eq_some hh
    obtain ⟨index, hi, he⟩ := List.mem_range'.mp hm
    simp only [Option.map_some, Option.getD_some]
    omega

theorem reverseReady_candidate_step {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (target : Nat) (htarget : 0 < target) (htargetBound : target ≤ size) :
    let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
    let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
    let cap := logicalHeap q capWords state.heap (base + remaining)
    (packingRun (callInput q full command) containing 105 state).heap (BitVec.ofNat bits (childBase header q + target)) =
      if parent = target ∧ count < cap then BitVec.ofNat bits (remaining + 1)
      else state.heap (BitVec.ofNat bits (childBase header q + target)) := by
  let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
  let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
  let cap := logicalHeap q capWords state.heap (base + remaining)
  have hpBound : parent ≤ size := ready.data.parentBound remaining (by have hh := ready.bound; omega)
  have htargetFit : Fits bits (childBase header q + target) := (Nat.le_succ _).trans_lt (layout.targetFits target htargetBound)
  have hparentFit : Fits bits (childBase header q + parent) := (Nat.le_succ _).trans_lt (layout.targetFits parent hpBound)
  have hneH : BitVec.ofNat bits (childBase header q + target) ≠ BitVec.ofNat bits (header + 8) := by
    apply (ofNat_injective_of_fit _ _ htargetFit (layout.headerFits 8 (by decide))).not.mpr
    unfold childBase
    omega
  rw [reverseReady_heap em layout command configuration state ready, reverseStepHeap, Function.update_of_ne hneH]
  change Function.update state.heap (BitVec.ofNat bits (childBase header q + parent))
      (pushedValue remaining parent cap count (state.heap (BitVec.ofNat bits (childBase header q + parent))))
      (BitVec.ofNat bits (childBase header q + target)) =
    if parent = target ∧ count < cap then BitVec.ofNat bits (remaining + 1)
      else state.heap (BitVec.ofNat bits (childBase header q + target))
  by_cases hmatch : parent = target
  · rw [hmatch, Function.update_self]
    have ht : target ≠ 0 := by omega
    by_cases hs : count < cap
    · have hsub : cap - count ≠ 0 := by omega
      simp [pushedValue, ht, hs, hsub]
    · have hsub : cap - count = 0 := by omega
      simp [pushedValue, ht, hs, hsub]
  · have hne : BitVec.ofNat bits (childBase header q + target) ≠ BitVec.ofNat bits (childBase header q + parent) := by
      apply (ofNat_injective_of_fit _ _ htargetFit hparentFit).not.mpr
      omega
    rw [Function.update_of_ne hne]
    simp only [hmatch, false_and, ite_false]

theorem actual_reverse_capacity_frame {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (clock : Nat) (hc : clock ≤ 105 * size + 5) (address : Nat) (ha : address < capWords) :
    logicalHeap q capWords (packingRun (callInput q full command) containing clock state).heap address =
      logicalHeap q capWords state.heap address := by
  apply PSTRRepairHeap.logical_frame state.heap _ capWords 0 (header + 8) address
    (by have hb := layout.bits8; omega) layout.positive layout.capacityFits
    (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide))
    (by have hm := layout.metadata_le; omega) ?_ (by omega)
  intro physical hphysical
  exact actual_reverse_loop_frame em layout command configuration state ready clock hc physical
    ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits) (.inl hphysical)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
