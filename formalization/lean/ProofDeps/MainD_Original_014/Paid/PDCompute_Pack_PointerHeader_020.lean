module
public import Paid.PDCompute_Pack_PointerMemory_017

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (storeSlotResult)

def pointerValues (values : ℕ → Cell) (base result : ℕ) : ℕ → Cell :=
  Function.update (Function.update (Function.update values outputStart (.natural result))
    outputCursor (.natural result)) sourceCursor (.natural (base+48))

theorem pointerStores_header (before : State) (base result : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (value : before.register .total=.natural result) :
    Header (pointerStoresResult before base) base (pointerValues values base result) := by
  let first:=storeSlotResult before base outputStart .total
  let second:=storeSlotResult first base outputCursor .total
  let arithmetic:=sourcePointerResult second base
  have header1:=header_store_result header outputStart .total
  have header2:=header_store_result header1 outputCursor .total
  have header3 : Header arithmetic base
      (Function.update (Function.update values outputStart (before.register .total)) outputCursor (first.register .total)) := header2
  have final:=header_store_result header3 sourceCursor .total
  have firstValue : first.register .total=.natural result := by simp [first,storeSlotResult,value]
  have lastValue : arithmetic.register .total=.natural (base+48) := by simp [arithmetic,sourcePointerResult,State.set]
  change Header (pointerStoresResult before base) base
    (Function.update (Function.update (Function.update values outputStart (before.register .total))
      outputCursor (first.register .total)) sourceCursor (arithmetic.register .total)) at final
  rw [value,firstValue,lastValue] at final
  exact final

end PDCompute.Pack
