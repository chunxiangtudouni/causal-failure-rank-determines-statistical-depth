module
public import Paid.PDCompute_Pack_RowModels_049

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

/-- Factual per-entry heap representations imply the corresponding
actual dense contiguous heap; this computes no serialized answer. -/
theorem denseEntries_heap (state : State) (entries : List MenuEntry) (source : ℕ)
    (represented : ∀ (index : ℕ) (inside : index<entries.length),
      HeapList state (source+6*index) (denseEncodeEntry entries[index])) :
    HeapList state source (denseEntries entries) := by
  induction entries generalizing source with
  | nil=>apply HeapList.of_values <;> intro offset bound <;> simp [denseEntries] at bound
  | cons entry entries ih=>
    have first : HeapList state source (denseEncodeEntry entry):=by
      have got:=represented 0 (by simp)
      change HeapList state (source+6*0) (denseEncodeEntry entry) at got
      simpa only [Nat.mul_zero,Nat.add_zero] using got
    have tailRepresented : ∀ (index : ℕ) (inside : index<entries.length),
        HeapList state (source+6+6*index) (denseEncodeEntry entries[index]) := by
      intro index inside
      have got:=represented (index+1) (by simp only [List.length_cons];omega)
      have addressEq : source+6*(index+1)=source+6+6*index:=by omega
      simpa only [addressEq,List.getElem_cons_succ] using got
    have tail:=ih (source+6) tailRepresented
    have result:=first.append (by simpa only [denseEncodeEntry_length,entryWords] using tail)
    exact result

theorem denseRows_heap (state : State) (rows : List MenuRow) (source columns : ℕ)
    (width : ∀ row∈rows,row.size=columns)
    (represented : ∀ (index : ℕ) (inside : index<rows.length),
      HeapList state (source+6*columns*index) (denseEntries rows[index].toList)) :
    HeapList state source (denseRows rows) := by
  induction rows generalizing source with
  | nil=>apply HeapList.of_values <;> intro offset bound <;> simp [denseRows] at bound
  | cons row rows ih=>
    have currentWidth:=width row (by simp)
    have tailWidth : ∀ row∈rows,row.size=columns:=fun row member=>width row (by simp [member])
    have first : HeapList state source (denseEntries row.toList):=by
      have got:=represented 0 (by simp)
      change HeapList state (source+6*columns*0) (denseEntries row.toList) at got
      simpa only [Nat.mul_zero,Nat.add_zero] using got
    have tailRepresented : ∀ (index : ℕ) (inside : index<rows.length),
        HeapList state (source+6*columns+6*columns*index) (denseEntries rows[index].toList) := by
      intro index inside
      have got:=represented (index+1) (by simp only [List.length_cons];omega)
      have addressEq : source+6*columns*(index+1)=source+6*columns+6*columns*index:=by
        simp only [Nat.mul_add,Nat.mul_one]
        omega
      simpa only [addressEq,List.getElem_cons_succ] using got
    have tail:=ih (source+6*columns) tailWidth tailRepresented
    have result:=first.append (by simpa only [denseEntries_length,Array.length_toList,currentWidth] using tail)
    exact result

theorem denseTable_heap (state : State) (table : MenuTable) (base k : ℕ)
    (columns : ∀ row∈table,row.size=k+1)
    (represented : ∀ (row : ℕ) (rowBound : row<table.size) (column : ℕ) (columnBound : column<table[row].size),
      HeapList state (cellBase base k row column) (denseEncodeEntry table[row][column])) :
    HeapList state (tableBase base) (denseRows table.toList) := by
  have width : ∀ row∈table.toList,row.size=k+1:=by simpa only [Array.mem_toList_iff] using columns
  apply denseRows_heap state table.toList (tableBase base) (k+1) width
  intro row rowBound
  apply denseEntries_heap state table.toList[row].toList (tableBase base+6*(k+1)*row)
  intro column columnBound
  have rowInside : row<table.size:=by simpa only [Array.length_toList] using rowBound
  have columnInside : column<table[row].size:=by
    simpa only [Array.length_toList,Array.getElem_toList] using columnBound
  have got:=represented row rowInside column columnInside
  have addressEq : cellBase base k row column=tableBase base+6*(k+1)*row+6*column := by
    unfold cellBase entryWords
    ring
  simpa only [addressEq,Array.getElem_toList] using got

end PDCompute.Pack
