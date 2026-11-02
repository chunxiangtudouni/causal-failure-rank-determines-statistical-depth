module

public import Paid.PDLower_CalibrationCompute_HeaderState_017
public import Paid.PDLower_CalibrationCompute_Constants_021

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Actual scalar call arguments only. Old live workspace cells are
allowed; cached outputs and successful phase runs are not arguments. -/
structure CallArguments (P : Parameters) (base endpoints returnPC : ℕ) (state : State) : Prop where
  fresh : state.register .fresh = .natural base
  old : state.register .old = .natural returnPC
  address : state.register .address = .natural endpoints
  total : state.register .total = .natural P.certificate.M
  index : state.register .index = .natural P.certificate.Q
  value : state.register .value = .rational P.certificate.gamma

theorem originalEntry_arguments {P : Parameters} {base endpoints returnPC : ℕ} {state : State}
    (entry : Entry P base endpoints returnPC state) : CallArguments P base endpoints returnPC state :=
  ⟨entry.1,entry.2.1,entry.2.2.1,entry.2.2.2.1,entry.2.2.2.2.1,entry.2.2.2.2.2.1⟩

theorem Header.At.loadResult {header : Header} {state : State} {base : ℕ}
    (represented : header.At state base) (offset : ℕ) (target : Register) :
    header.At (loadSlotResult state base offset target) base := represented

theorem Header.At.storeResult {header updated : Header} {state : State} {base : ℕ}
    (represented : header.At state base) (offset : ℕ) (inside : offset < 16)
    (source : Register) (value : Cell) (sourceValue : state.register source = value)
    (updatedCells : header.cells.set offset value = updated.cells) :
    updated.At (storeSlotResult state base offset source) base := by
  have oldBound : offset < header.cells.length := by simpa only [Header.cells_length] using inside
  have written := HeapList.write represented offset oldBound (state.register source)
  simpa only [Header.At,HeapList,heapSegment,storeSlotResult,writeCell,sourceValue,updatedCells] using written

theorem Header.At.constantResult {header updated : Header} {state : State} {base : ℕ}
    (represented : header.At state base) (offset : ℕ) (inside : offset < 16) (value : Cell)
    (updatedCells : header.cells.set offset value = updated.cells) :
    updated.At (constantSlotResult state base offset value) base := by
  have oldBound : offset < header.cells.length := by simpa only [Header.cells_length] using inside
  have written := HeapList.write represented offset oldBound value
  simpa only [Header.At,HeapList,heapSegment,constantSlotResult,storeSlotResult,State.set,writeCell,
    Function.update_self,updatedCells] using written

def sumStartResult (before : State) (base : ℕ) : State :=
  constantSlotResult (constantSlotResult before base 11 (.rational 0)) base 7 (.natural 0)

theorem sumStart_execute (input : List Cell) (before : State) (base : ℕ)
    (fresh : before.register .fresh = .natural base) :
    linearExecute input (basicBlock .sumStart).body before = some (sumStartResult before base) := by
  change linearExecute input (constantSlot 11 (.rational 0) ++ constantSlot 7 (.natural 0)) before = _
  rw [linearExecute_append,constantSlot_execute input before base 11 (.rational 0) fresh,Option.bind_some]
  exact constantSlot_execute input _ base 7 (.natural 0) ((constantSlot_fresh ..).trans fresh)

theorem sumStart_header {header : Header} {before : State} {base : ℕ}
    (represented : header.At before base) :
    ({header with q := 0,cursor := 0}).At (sumStartResult before base) base := by
  have first : ({header with q := 0}).At (constantSlotResult before base 11 (.rational 0)) base :=
    represented.constantResult 11 (by decide) (.rational 0) (Header.set_q header 0)
  exact first.constantResult 7 (by decide) (.natural 0) (Header.set_cursor _ 0)

end PDLower.CalibrationCompute
