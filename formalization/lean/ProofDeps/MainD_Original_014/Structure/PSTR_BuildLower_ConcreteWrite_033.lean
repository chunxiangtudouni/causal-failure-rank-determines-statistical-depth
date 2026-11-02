module

public import Structure.PSTR_BuildLower_ConcreteHeap_028

/-! Concrete write dispatch has the actual frozen replacement semantics.
The packed pointer is really reloaded twice. The old logical cutoff C0
is read from bank3 and is not silently replaced by physical C. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
variable {bits : Nat}

def writeViewHeap (q : Nat) (state : WordState bits) (pointer : Register) : BitVec bits → BitVec bits :=
  if DispatchRun.ordinaryCase pointer state then
    Function.update state.heap (Ordinary.targetAddress state pointer) (state.register .value)
  else PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q)
    ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q) (state.register .value) state.heap

theorem write_result_heap (q C : Nat) (rom : PhysicalROM) (left : List PackingOp)
    (pointer : Register) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (hcapacity : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ C)
    (hscale : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q))
    (hnext : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + registerOffset pointer)
    (hbankFit : Fits bits ((state.register .address).toNat + registerOffset pointer)) :
    (DispatchRun.result rom left (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer))
      (Ordinary.write pointer) pointer state).heap = writeViewHeap q state pointer := by
  let tested := executeOps rom (memoryClassify pointer
    (5 * (left.length + 9 + (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)).length + 3))) state
  have ht := memoryClassify_prefix_frame rom pointer
    (5 * (left.length + 9 + (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)).length + 3)) state
    (memoryClassify pointer (5 * (left.length + 9 + (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)).length + 3))).length
  rw [List.take_length] at ht
  have htHeap : tested.heap = state.heap := ht.1
  have htBase : tested.register .address = state.register .address := ht.2
  have htValue : tested.register .value = state.register .value := memoryClassify_value rom pointer _ state
  have htPointer : PA06A19PrepareBankPacked021.pointer (registerOffset pointer) tested =
      Ordinary.pointerValue state pointer := by
    simp only [PA06A19PrepareBankPacked021.pointer, Ordinary.pointerValue, htHeap, htBase]
  by_cases hg : DispatchRun.ordinaryCase pointer state
  · simp only [DispatchRun.result, writeViewHeap, hg, ite_true]
    rw [Ordinary.write_heap]
    change Function.update tested.heap (Ordinary.targetAddress tested pointer) (tested.register .value) = _
    rw [htHeap, htValue]
    congr 1
  · have hlt : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat := Nat.lt_of_not_ge hg
    simp only [DispatchRun.result, writeViewHeap, hg, ite_false]
    change (executeOps rom (PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)) tested).heap = _
    have wh := PA06A19PrepareBankPacked021.safeWrite_heap q C (registerOffset pointer) rom tested
      (by rwa [htHeap]) hq hb hw (by rw [htPointer]; exact hlt.trans_le hcapacity)
      (by rw [htPointer]; exact hscale hlt) (by rw [htPointer]; exact hnext hlt)
      (by rwa [htBase]) (by rwa [htBase])
    rw [wh, htPointer, htHeap, htValue]

theorem write_call_heap (q C : Nat) (rom : PhysicalROM) (left right : List PackingOp)
    (pointer : Register) (state : WordState bits)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hq : 0 < q) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits)
    (hcapacity : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ C)
    (hscale : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q))
    (hnext : (Ordinary.pointerValue state pointer).toNat <
        (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat →
      Fits bits ((Ordinary.pointerValue state pointer).toNat * CapacityBits.width q / bits + 4 + 1))
    (hbank : 4 + packedCapacityWords q C bits + 1 ≤ (state.register .address).toNat + registerOffset pointer)
    (hbankFit : Fits bits ((state.register .address).toNat + registerOffset pointer))
    (hcode : WordsFit bits (packingCode (left ++ write left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ write left.length pointer ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    let packed := PA06A19PrepareBankPacked021.safeWrite (registerOffset pointer)
    let count := DispatchRun.steps packed (Ordinary.write pointer) pointer state
    count ≤ 96 ∧ (packingRun rom (left ++ write left.length pointer ++ right) count state).heap = writeViewHeap q state pointer := by
  have result := write_call rom left right pointer state hcode hpcfit hpc ha
  dsimp only at result ⊢
  exact ⟨result.1, (congrArg WordState.heap result.2).trans
    (write_result_heap q C rom left pointer state hh hq hb hw hcapacity hscale hnext hbank hbankFit)⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteHeap
