module

public import Paid.PDLower_CalibrationCompute_SavedArgs_018
public import Paid.PDLower_CalibrationCompute_Code_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def enterBasesResult (before : State) (base M : ℕ) : State :=
  let start := {before with
    pc := before.pc+6
    register := Function.update
      (Function.update
        (Function.update
          (Function.update
            (Function.update before.register .flag (.natural 2))
            .index (.natural (M*2)))
          .flag (.natural 3))
        .index (.natural (rowWidth M)))
      .old (.natural (firstRow base))}
  let first := storeSlotResult start base 9 .old
  let middle := {first with
    pc := first.pc+1
    register := Function.update first.register .total (.natural (secondRow base M))}
  let second := storeSlotResult middle base 10 .total
  let last := {second with
    pc := second.pc+1
    register := Function.update second.register .total (.natural (resultBase base M))}
  storeSlotResult last base 15 .total

theorem enterBases_execute (input : List Cell) (before : State) (base M : ℕ)
    (fresh : before.register .fresh = .natural base) (total : before.register .total = .natural M) :
    linearExecute input (basicBlock .enterBases).body before = some (enterBasesResult before base M) := by
  simp [basicBlock,linearExecute,storeSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    fresh,total,enterBasesResult,storeSlotResult,rowWidth,firstRow,secondRow,resultBase,Nat.add_assoc,two_mul,mul_two]

theorem enterBases_fresh (before : State) (base M : ℕ) :
    (enterBasesResult before base M).register .fresh = before.register .fresh := by
  simp [enterBasesResult,storeSlotResult]

theorem enterBases_output (before : State) (base M : ℕ) :
    (enterBasesResult before base M).output = before.output := rfl

theorem enterBases_pc (before : State) (base M : ℕ) :
    (enterBasesResult before base M).pc = before.pc+17 := by
  simp [enterBasesResult,storeSlotResult,Nat.add_assoc]

theorem enterBases_arguments {before : State} {base M : ℕ} {arguments : List Cell}
    (represented : HeapList before base arguments) (length : arguments.length = 5) :
    HeapList (enterBasesResult before base M) base arguments := by
  have avoid (index : ℕ) (inside : index < arguments.length) (offset : ℕ) (later : 5 ≤ offset) :
      base+index ≠ base+offset := by rw [length] at inside; omega
  apply HeapList.of_values
  · intro index inside
    simpa only [enterBasesResult,storeSlotResult,Finset.mem_insert] using
      Or.inr (Or.inr (Or.inr (represented.1 index inside)))
  · intro index inside
    simp only [enterBasesResult,storeSlotResult,Function.update_apply,
      avoid index inside 15 (by omega),avoid index inside 10 (by omega),avoid index inside 9 (by omega),↓reduceIte]
    exact HeapList.value represented index inside

end PDLower.CalibrationCompute
