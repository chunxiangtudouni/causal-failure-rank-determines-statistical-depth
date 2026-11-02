module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009al

/-! Exact ascending-first candidate after the actual reverse runtime loop.
The scan predicate is read from this same incoming heap; all later source
reads are proved equal by real prefix frames, including packed VOID payloads. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def parentHit {bits : Nat} (q capWords base counts parents target : Nat)
    (heap : BitVec bits → BitVec bits) (node : Nat) : Bool :=
  decide ((heap (BitVec.ofNat bits (parents + (node + 1)))).toNat = target ∧
    (heap (BitVec.ofNat bits (counts + node))).toNat < logicalHeap q capWords heap (base + node))

theorem actual_reverse_candidate_iterations {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (target : Nat) (htarget : 0 < target) (htargetBound : target ≤ size)
    (hz : state.heap (BitVec.ofNat bits (childBase header q + target)) = BitVec.ofNat bits 0)
    (iterations : Nat) (hi : iterations ≤ size) :
    (packingRun (callInput q full command) containing (105 * iterations) state).heap
        (BitVec.ofNat bits (childBase header q + target)) =
      BitVec.ofNat bits (childSuffix size (size - iterations) (parentHit q capWords base counts parents target state.heap)) := by
  induction iterations with
  | zero => simpa only [Nat.mul_zero, packingRun, Nat.sub_zero, childSuffix_init] using hz
  | succ iterations ih =>
    let rom := callInput q full command
    let middle := packingRun rom containing (105 * iterations) state
    let node := size - (iterations + 1)
    have hiter : iterations ≤ size := by omega
    have hnode : node < size := by dsimp only [node]; omega
    have hr : node + 1 + iterations = size := by dsimp only [node]; omega
    have rd : ReverseReady full configuration origin capWords header base counts parents size (node + 1) middle := by
      apply reverseReady_iterations em layout command configuration state
      simpa only [hr] using ready
    have hpfit : Fits bits (parents + (node + 1)) :=
      (show parents + (node + 1) ≤ header + 8 by have hp := layout.parentsEnd; omega).trans_lt (layout.headerFits 8 (by decide))
    have hcfit : Fits bits (counts + node) :=
      (show counts + node ≤ header + 8 by have hp := layout.countsEnd; omega).trans_lt (layout.headerFits 8 (by decide))
    have hclock : 105 * iterations ≤ 105 * size + 5 := by omega
    have hparent := actual_reverse_loop_frame em layout command configuration state ready (105 * iterations) hclock
      (parents + (node + 1)) hpfit (.inl (by have hp := layout.parentsEnd; omega))
    have hcount := actual_reverse_loop_frame em layout command configuration state ready (105 * iterations) hclock
      (counts + node) hcfit (.inl (by have hp := layout.countsEnd; omega))
    have hcap := actual_reverse_capacity_frame em layout command configuration state ready (105 * iterations) hclock
      (base + node) (by have hp := layout.payloadBound; omega)
    have hstep := reverseReady_candidate_step em layout command configuration middle rd target htarget htargetBound
    dsimp only at hstep
    rw [hparent, hcount, hcap] at hstep
    have hh := ih hiter
    change middle.heap _ = _ at hh
    rw [show 105 * (iterations + 1) = 105 * iterations + 105 by omega, run_add, hstep, hh]
    have he : size - iterations = node + 1 := by dsimp only [node]; omega
    rw [he, show size - (iterations + 1) = node from rfl, childSuffix_step size node _ hnode]
    simp only [parentHit, decide_eq_true_eq]
    split <;> rfl

theorem actual_reverse_candidate {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state)
    (target : Nat) (htarget : 0 < target) (htargetBound : target ≤ size)
    (hz : state.heap (BitVec.ofNat bits (childBase header q + target)) = BitVec.ofNat bits 0) :
    (packingRun (callInput q full command) containing (105 * size + 5) state).heap
        (BitVec.ofNat bits (childBase header q + target)) =
      BitVec.ofNat bits (childSuffix size 0 (parentHit q capWords base counts parents target state.heap)) := by
  let rom := callInput q full command
  let middle := packingRun rom containing (105 * size) state
  have rd : ReverseReady full configuration origin capWords header base counts parents size 0 middle := by
    simpa only [Nat.zero_add] using reverseReady_iterations em layout command configuration state
      (by simpa only [Nat.zero_add] using ready : ReverseReady full configuration origin capWords header base counts parents size (0 + size) state)
  rw [run_add, fetched_reverse_test em rom middle rd.pc rd.active]
  rw [(reverseTest_result rom origin header 0 middle ((show 0 ≤ 1 by decide).trans_lt layout.oneFits)
    rd.address rd.pc rd.counter).2.2]
  simpa only [Nat.sub_self] using actual_reverse_candidate_iterations em layout command configuration state ready target htarget htargetBound hz size le_rfl

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
