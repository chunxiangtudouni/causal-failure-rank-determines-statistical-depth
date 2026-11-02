module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009s

/-! Arbitrarily many genuine runtime reverse iterations, without an unrolled
dimension-dependent program. Each iteration consumes the actual heap counter
and the same original packed representation established by the prior run. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem reverseReady_iterations {bits q origin capWords heapWords header base counts parents size remaining iterations : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + iterations) state) :
    ReverseReady full configuration origin capWords header base counts parents size remaining
      (packingRun (callInput q full command) containing (105 * iterations) state) := by
  induction iterations generalizing state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, packingRun] using ready
  | succ iterations ih =>
    have rd : ReverseReady full configuration origin capWords header base counts parents size ((remaining + iterations) + 1) state := by
      simpa only [Nat.add_assoc] using ready
    have next := reverseReady_step em layout command configuration state rd
    rw [show 105 * (iterations + 1) = 105 + 105 * iterations by omega, run_add]
    exact ih _ next

theorem actual_reverse_loop {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size size state) :
    let after := packingRun (callInput q full command) containing (105 * size + 5) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 105)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits 0 ∧
      ReverseHeapData full configuration capWords header base counts parents size after.heap := by
  let rom := callInput q full command
  let looped := packingRun rom containing (105 * size) state
  have hend : ReverseReady full configuration origin capWords header base counts parents size 0 looped := by
    simpa only [Nat.zero_add] using reverseReady_iterations em layout command configuration state
      (by simpa only [Nat.zero_add] using ready :
        ReverseReady full configuration origin capWords header base counts parents size (0 + size) state)
  have ht := reverseTest_result rom origin header 0 looped ((show 0 ≤ 1 by decide).trans_lt layout.oneFits)
    hend.address hend.pc hend.counter
  have hrun : packingRun rom containing (105 * size + 5) state = executeOps rom (reverseTest origin) looped := by
    rw [run_add]
    exact fetched_reverse_test em rom looped hend.pc hend.active
  dsimp only
  rw [hrun]
  refine ⟨by rw [executeOps_halted, hend.active], ?_, ht.2.1, ?_, ?_⟩
  · simpa only [ite_true] using ht.1
  · rw [ht.2.2]
    exact hend.counter
  · rw [ht.2.2]
    exact hend.data

theorem actual_reverse_loop_trace {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (105 * size + 5) state).length ≤ 1320 * (size + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (105 * size + 5) state
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
