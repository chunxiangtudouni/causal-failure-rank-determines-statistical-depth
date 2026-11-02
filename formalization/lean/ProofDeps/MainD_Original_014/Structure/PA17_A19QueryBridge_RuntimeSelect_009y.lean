module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009x

/-! Complete fixed164op parent-building kernel, from original represented
heap and same-call header/cache/parent materialization. The real clear and
initialization precede the runtime reverse scan; no Ready/scratch oracle is
an entry assumption of this concrete theorem. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def parentSteps (size : Nat) : Nat := clearSteps size + 38 + (105 * size + 5)

theorem parentSteps_eq (size : Nat) : parentSteps size = 112 * size + 66 := by unfold parentSteps clearSteps; omega

theorem actual_parent_kernel {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (row budget : Nat) (state : WordState bits)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hwidth : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.heap (BitVec.ofNat bits (PSTRQueryLayout.physicalWorkspace full capWords bits + 13)) =
      lowMask bits (CapacityBits.width q))
    (hparentBound : ∀ node < size, (state.heap (BitVec.ofNat bits (parents + (node + 1)))).toNat ≤ size)
    (hcounts : counts = header - (size + (size + 1))) (hparents : parents = header - (size + 1))
    (hbase : base = row + budget * (size + 1) + 1) (hbudget : budget ≤ q + 1)
    (hrow : state.heap (BitVec.ofNat bits header) = BitVec.ofNat bits row)
    (hselected : state.heap (BitVec.ofNat bits (header + 6)) = BitVec.ofNat bits budget)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full command) containing (parentSteps size) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits (5 * (origin + 164)) ∧
      after.register .address = BitVec.ofNat bits header ∧
      after.heap (BitVec.ofNat bits (header + 8)) = BitVec.ofNat bits 0 ∧
      ReverseHeapData full configuration capWords header base counts parents size after.heap := by
  let prepared := packingRun (callInput q full command) containing (clearSteps size + 38) state
  have hi := actual_initial_ready em layout command configuration row budget state rep hwidth hmask hparentBound hcounts hparents
    hbase hbudget hrow hselected hh hp ha
  have hend := actual_reverse_loop (parent_reverse_embedded em) layout command configuration prepared hi.1
  dsimp only
  rw [parentSteps, run_add]
  exact ⟨hend.1, by simpa only [Nat.add_assoc, Nat.reduceAdd] using hend.2.1,
    hend.2.2.1, hend.2.2.2.1, hend.2.2.2.2⟩

theorem actual_parent_trace {bits : Nat} (rom : PhysicalROM) (containing : List PackingOp) (size : Nat) (state : WordState bits) :
    (packingDynamicTrace rom containing (parentSteps size) state).length ≤ 2136 * (size + 1) := by
  have hh := packingDynamicTrace_length_le rom containing (parentSteps size) state
  rw [parentSteps_eq] at hh ⊢
  omega

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
