module
public import Paid.PDCompute_Pack_CounterTrace_014
public import Paid.PDCompute_Pack_PointerStores_010
public import Paid.PDCompute_Pack_Fragments_018

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDLower.CalibrationCompute (loadSlot storeSlot)

def initializeHeaderCode : List Instruction :=
  copyPlusOneCode 3 rowRemaining++copyPlusOneCode 4 columnsPerRow++pointerArithmeticCode++pointerStoresCode

def tableLengthCode : List Instruction :=
  loadSlot outputStart .old++writeSlots [rowRemaining]++storeSlot outputCursor .old

theorem initializeHeaderCode_length : initializeHeaderCode.length=51 := by
  simp only [initializeHeaderCode,List.length_append,copyPlusOneCode_length,pointerArithmeticCode_length,pointerStoresCode_length]
theorem tableLengthCode_length : tableLengthCode.length=12 := rfl

theorem initialize_decompose : initializeCode=initializeHeaderCode++tableLengthCode := by
  simp only [initializeCode,initializeHeaderCode,tableLengthCode,copyPlusOneCode,pointerArithmeticCode,
    pointerStoresCode,sourcePointerCode,List.append_assoc]

theorem fetch_initializeHeader (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program origin initializeHeaderCode := by
  have init:=fetch_initialize program origin fetched
  rw [initialize_decompose] at init
  exact init.append_left

theorem fetch_tableLength (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (serializerCode origin)) : FetchesCode program (origin+51) tableLengthCode := by
  have init:=fetch_initialize program origin fetched
  rw [initialize_decompose] at init
  simpa only [initializeHeaderCode_length] using init.append_right

end PDCompute.Pack
