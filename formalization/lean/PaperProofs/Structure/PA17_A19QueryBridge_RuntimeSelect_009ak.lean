module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009aj

/-! Real91op descent fuel induction and ACTIVE exit, with every data fact
produced by preceding actual iterations. No unrolled dimensioned program
or supplied traversal is executed by this loop. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descReady_iterations {bits q origin capWords heapWords header base counts parents size remaining iterations : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + iterations) state) :
    DescReady full configuration origin capWords header base counts parents size remaining
      (packingRun (callInput q full command) containing (91 * iterations) state) := by
  induction iterations generalizing state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, packingRun] using ready
  | succ iterations ih =>
    have rd : DescReady full configuration origin capWords header base counts parents size ((remaining + iterations) + 1) state := by
      simpa only [Nat.add_assoc] using ready
    have next := descReady_step em layout command configuration state rd
    rw [show 91 * (iterations + 1) = 91 + 91 * iterations by omega, run_add]
    exact ih _ next

theorem actual_desc_loop {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size size state) :
    let after := packingRun (callInput q full command) containing (descendSteps size) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 91)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.heap (BitVec.ofNat bits (header + 13)) = BitVec.ofNat bits 0 ∧
      ReverseHeapData full configuration capWords header base counts parents size after.heap ∧
      CandidateBounded header q size after.heap ∧
      after.heap (BitVec.ofNat bits (header + 14)) = BitVec.ofNat bits (nodeSlot header q size) ∧
      after.heap (BitVec.ofNat bits (header + 15)) = BitVec.ofNat bits (toolSlot header q size) := by
  let rom := callInput q full command
  let looped := packingRun rom containing (91 * size) state
  have r0 : DescReady full configuration origin capWords header base counts parents size (0 + size) state := by
    simpa only [Nat.zero_add] using ready
  have hend : DescReady full configuration origin capWords header base counts parents size 0 looped :=
    descReady_iterations em layout command configuration state r0
  have ht := descendTest_result rom origin header 0 looped ((show 0 ≤ 1 by decide).trans_lt layout.oneFits)
    hend.address hend.pc hend.fuel
  have hrun : packingRun rom containing (descendSteps size) state = executeOps rom (descendTest origin) looped := by
    rw [descendSteps, run_add]
    exact fetched_desc_test em rom looped hend.pc hend.active
  dsimp only
  rw [hrun]
  refine ⟨by rw [executeOps_halted, hend.active], ?_, ht.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_true] using ht.1
  · rw [ht.2.2]
    exact hend.fuel
  · rw [ht.2.2]
    exact hend.data
  · rw [ht.2.2]
    exact hend.candidates
  · rw [ht.2.2]
    exact hend.nodePointer
  · rw [ht.2.2]
    exact hend.toolPointer

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
