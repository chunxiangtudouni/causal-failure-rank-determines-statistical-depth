module
public import Paid.PDCompute_Pack_Layout_001
public import Paid.PDCompute_SolverDenseBlock_071

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (loadSlot storeSlot)

/-- Static expansion of six original ISA operations per selected header
cell, definitionally the producer's inverse-stream primitive. The slots
are a fixed literal list, never generated from the runtime table. -/
def writeSlots (slots : List ℕ) : List Instruction := slots.flatMap fun source =>
  loadSlot source .total++[.store .old .total,.constant .flag (.natural 1),.natOp .add .old .old .flag]

def decrementSlot (slot : ℕ) : List Instruction :=
  loadSlot slot .index++[.constant .flag (.natural 1),.natOp .subtract .index .index .flag]++storeSlot slot .index

/-- Construct the actual result base from saved n/k, save streaming
pointers, and really write the original table-length word. -/
def initializeCode : List Instruction :=
  copySlot 3 rowRemaining++addNatSlot rowRemaining 1++
  copySlot 4 columnsPerRow++addNatSlot columnsPerRow 1++
  loadSlot rowRemaining .index++loadSlot columnsPerRow .value++
  [.natOp .multiply .total .index .value,.constant .flag (.natural 6),
   .natOp .multiply .total .total .flag,.constant .flag (.natural 48),
   .natOp .add .total .total .flag,.natOp .add .total .total .fresh]++
  storeSlot outputStart .total++storeSlot outputCursor .total++
  [.constant .total (.natural 48),.natOp .add .total .fresh .total]++storeSlot sourceCursor .total++
  loadSlot outputStart .old++writeSlots [rowRemaining]++storeSlot outputCursor .old

def startRowCode : List Instruction :=
  loadSlot outputCursor .old++writeSlots [columnsPerRow]++storeSlot outputCursor .old++
  copySlot columnsPerRow columnRemaining

def readEntryCode : List Instruction :=
  loadSlot sourceCursor .old++denseReadBlockCode entryStart 6++storeSlot sourceCursor .old++
  loadSlot outputCursor .old++loadSlot entryStart .value++
  [.constant .flag (.natural 2),.natOp .subtract .value .flag .value]

def returnCode : List Instruction :=
  loadSlot 1 .old++loadSlot outputCursor .index++loadSlot outputStart .address++
  [.natOp .subtract .index .index .address,.jumpIndirect .old]

/-- 233 fixed origin-generated literal original instructions. Branches
implement real nested loops; test entries copy six words, finish/abandon
entries copy exactly four. Every move/store/jump remains a real step. -/
def serializerCode (origin : ℕ) : List Instruction :=
  initializeCode++
  loadSlot rowRemaining .index++[.branchZero .index (origin+222) (origin+67)]++
  startRowCode++
  loadSlot columnRemaining .index++[.branchZero .index (origin+213) (origin+89)]++
  readEntryCode++[.branchZero .value (origin+165) (origin+140)]++
  writeSlots [24,27,28,29]++[.jump (origin+201)]++writeSlots [24,25,26,27,28,29]++
  storeSlot outputCursor .old++decrementSlot columnRemaining++[.jump (origin+85)]++
  decrementSlot rowRemaining++[.jump (origin+63)]++returnCode

theorem writeSlots_length (slots : List ℕ) : (writeSlots slots).length=6*slots.length := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    simp only [writeSlots,List.flatMap_cons,List.length_append,loadSlot,List.length_cons,List.length_nil] at ih ⊢
    omega

theorem decrementSlot_length (slot : ℕ) : (decrementSlot slot).length=8 := rfl
theorem initializeCode_length : initializeCode.length=63 := rfl
theorem startRowCode_length : startRowCode.length=18 := rfl
theorem readEntryCode_length : readEntryCode.length=50 := rfl
theorem returnCode_length : returnCode.length=11 := rfl
theorem serializerCode_length (origin : ℕ) : (serializerCode origin).length=233 := by
  simp only [serializerCode,List.length_append,initializeCode_length,startRowCode_length,
    readEntryCode_length,returnCode_length,writeSlots_length,decrementSlot_length,
    loadSlot,storeSlot,List.length_cons,List.length_nil]

end PDCompute.Pack
