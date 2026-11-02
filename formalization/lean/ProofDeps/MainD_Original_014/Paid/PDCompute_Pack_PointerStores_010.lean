module
public import Paid.PDCompute_Pack_ArithmeticMemory_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute linearExecute_append storeSlot storeSlotResult)

def sourcePointerCode : List Instruction :=
  [.constant .total (.natural 48),.natOp .add .total .fresh .total]

def sourcePointerResult (before : State) (base : ℕ) : State :=
  ({before with pc:=before.pc+2}).set .total (.natural (base+48))

theorem sourcePointer_execute (input : List Cell) (before : State) (base : ℕ)
    (hbase : before.register .fresh=.natural base) :
    linearExecute input sourcePointerCode before=some (sourcePointerResult before base) := by
  simp [sourcePointerCode,sourcePointerResult,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,Nat.add_assoc]

def pointerStoresCode : List Instruction :=
  storeSlot outputStart .total++storeSlot outputCursor .total++sourcePointerCode++storeSlot sourceCursor .total

def pointerStoresResult (before : State) (base : ℕ) : State :=
  let first:=storeSlotResult before base outputStart .total
  let second:=storeSlotResult first base outputCursor .total
  storeSlotResult (sourcePointerResult second base) base sourceCursor .total

theorem pointerStoresCode_length : pointerStoresCode.length=11 := rfl

theorem pointerStores_execute (input : List Cell) (before : State) (base : ℕ)
    (hbase : before.register .fresh=.natural base) :
    linearExecute input pointerStoresCode before=some (pointerStoresResult before base) := by
  let first:=storeSlotResult before base outputStart .total
  let second:=storeSlotResult first base outputCursor .total
  let arithmetic:=sourcePointerResult second base
  have firstBase : first.register .fresh=.natural base := by simp [first,storeSlotResult,hbase]
  have secondBase : second.register .fresh=.natural base := by simp [second,storeSlotResult,firstBase]
  have lastBase : arithmetic.register .fresh=.natural base := by simp [arithmetic,sourcePointerResult,State.set,secondBase]
  have one:=PDLower.CalibrationCompute.storeSlot_execute input before base outputStart .total hbase (by decide)
  have two:=PDLower.CalibrationCompute.storeSlot_execute input first base outputCursor .total firstBase (by decide)
  have three:=sourcePointer_execute input second base secondBase
  have four:=PDLower.CalibrationCompute.storeSlot_execute input arithmetic base sourceCursor .total lastBase (by decide)
  dsimp only [first] at two
  dsimp only [second,first] at three
  dsimp only [arithmetic,second,first] at four
  simp only [pointerStoresCode,pointerStoresResult,linearExecute_append,one,Option.bind_some,two,three,four]

theorem pointerStores_fields (before : State) (base result : ℕ)
    (value : before.register .total=.natural result) :
    (pointerStoresResult before base).heap=
      Function.update (Function.update (Function.update before.heap (base+outputStart) (.natural result))
        (base+outputCursor) (.natural result)) (base+sourceCursor) (.natural (base+48)) ∧
    (pointerStoresResult before base).live=insert (base+sourceCursor) (insert (base+outputCursor) (insert (base+outputStart) before.live)) ∧
    (pointerStoresResult before base).register .fresh=before.register .fresh ∧
    (pointerStoresResult before base).pc=before.pc+11 ∧
    (pointerStoresResult before base).output=before.output := by
  simp [pointerStoresResult,storeSlotResult,sourcePointerResult,State.set,value,Nat.add_assoc]

end PDCompute.Pack
