module

public import Paid.PDLower_CalibrationCompute_Append_016
public import Paid.PDLower_CalibrationCompute_Code_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def enterCacheResult (before : State) (base M cursor : ℕ) : State :=
  let loaded := loadSlotResult before base 2 .value
  let incremented := {loaded with
    pc := loaded.pc+2
    register := Function.update (Function.update loaded.register .flag (.natural 1))
      .value (.natural (M+1))}
  let pointed := loadSlotResult incremented base 15 .index
  let written := writeCell pointed cursor (.natural (M+1))
  let emitted := {written with pc := written.pc+1,output := written.output++[Cell.natural (M+1)]}
  let advanced := {emitted with
    pc := emitted.pc+1
    register := Function.update emitted.register .index (.natural (cursor+1))}
  let saved := storeSlotResult advanced base 15 .index
  let level := {saved with
    pc := saved.pc+1
    register := Function.update saved.register .value (.natural 1)}
  storeSlotResult level base 5 .value

theorem enterCache_execute (input : List Cell) (before : State) (base M cursor : ℕ)
    (fresh : before.register .fresh = .natural base)
    (sizeLive : base+2 ∈ before.live) (sizeValue : before.heap (base+2) = .natural M)
    (cursorLive : base+15 ∈ before.live) (cursorValue : before.heap (base+15) = .natural cursor) :
    linearExecute input (basicBlock .enterCache).body before = some (enterCacheResult before base M cursor) := by
  simp [basicBlock,constantSlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,fresh,sizeLive,sizeValue,cursorLive,cursorValue,enterCacheResult,
    loadSlotResult,storeSlotResult,writeCell,Nat.add_assoc]

theorem enterCache_output (before : State) (base M cursor : ℕ) :
    (enterCacheResult before base M cursor).output = before.output++[.natural (M+1)] := rfl

theorem enterCache_fresh (before : State) (base M cursor : ℕ) :
    (enterCacheResult before base M cursor).register .fresh = before.register .fresh := by
  simp [enterCacheResult,loadSlotResult,storeSlotResult,writeCell]

theorem enterCache_pc (before : State) (base M cursor : ℕ) :
    (enterCacheResult before base M cursor).pc = before.pc+18 := by
  simp [enterCacheResult,loadSlotResult,storeSlotResult,writeCell,Nat.add_assoc]

theorem enterCache_arguments {before : State} {base M : ℕ} {arguments : List Cell}
    (represented : HeapList before base arguments) (length : arguments.length = 5) :
    HeapList (enterCacheResult before base M (resultBase base M)) base arguments := by
  have avoid (index : ℕ) (inside : index < arguments.length) (offset : ℕ) (later : 5 ≤ offset) :
      base+index ≠ base+offset := by rw [length] at inside; omega
  have resultAvoid (index : ℕ) (inside : index < arguments.length) :
      base+index ≠ resultBase base M := by
    rw [length] at inside
    unfold resultBase rowWidth
    omega
  apply HeapList.of_values
  · intro index inside
    change base+index ∈ insert (base+5) (insert (base+15)
      (insert (resultBase base M) before.live))
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (represented.1 index inside)))
  · intro index inside
    simp only [enterCacheResult,loadSlotResult,storeSlotResult,writeCell,Function.update_apply,
      avoid index inside 5 (by omega),avoid index inside 15 (by omega),resultAvoid index inside,↓reduceIte]
    exact HeapList.value represented index inside

end PDLower.CalibrationCompute
