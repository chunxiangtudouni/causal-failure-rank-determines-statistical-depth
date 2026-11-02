module
public import Paid.PDCompute_Pack_StartRow_041
public import Paid.PDCompute_Pack_Sequence_046

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid PaperProofs.Paid.Computation 
open PDCompute.Solver hiding HeapList

def encodedRows (rows : List MenuRow) : List Cell:=rows.flatMap encodeRow
def denseRows (rows : List MenuRow) : List Cell:=rows.flatMap (fun row=>denseEntries row.toList)
def tableStable (slot : ℕ) : Prop:=entryStable slot ∧ slot≠rowRemaining

theorem encodeRow_eq (row : MenuRow) : encodeRow row=.natural row.size::encodedEntries row.toList := by
  simp [encodeRow,encodeList,encodedEntries]
theorem encodeTable_eq (table : MenuTable) : encodeTable table=.natural table.size::encodedRows table.toList := by
  simp [encodeTable,encodeList,encodedRows]

theorem denseRows_length (rows : List MenuRow) (columns : ℕ) (width : ∀ row∈rows,row.size=columns) :
    (denseRows rows).length=6*rows.length*columns := by
  induction rows with
  | nil=>simp [denseRows]
  | cons row rows ih=>
    have current:=width row (by simp)
    have tail : ∀ row∈rows,row.size=columns:=fun row member=>width row (by simp [member])
    have tailLength:=ih tail
    simp only [denseRows,List.flatMap_cons,List.length_append,denseEntries_length,Array.length_toList,List.length_cons] at tailLength ⊢
    rw [current]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
    omega

theorem startRowValues_source (values : ℕ → Cell) (pointer : ℕ) :
    startRowValues values pointer sourceCursor=values sourceCursor := by
  simp only [startRowValues,Function.update_of_ne (by decide : sourceCursor≠columnRemaining),
    Function.update_of_ne (by decide : sourceCursor≠outputCursor)]
theorem startRowValues_pointer (values : ℕ → Cell) (pointer : ℕ) :
    startRowValues values pointer outputCursor=.natural (pointer+1) := by
  simp only [startRowValues,Function.update_of_ne (by decide : outputCursor≠columnRemaining),Function.update_self]
theorem startRowValues_count (values : ℕ → Cell) (pointer : ℕ) :
    startRowValues values pointer columnRemaining=values columnsPerRow := by
  simp only [startRowValues,Function.update_self]
theorem startRowValues_stable (values : ℕ → Cell) (pointer slot : ℕ) (stable : entryStable slot) :
    startRowValues values pointer slot=values slot := by
  simp only [startRowValues,Function.update_of_ne stable.2.1,Function.update_of_ne stable.2.2.2]

theorem rowRemaining_entryStable : entryStable rowRemaining := by unfold entryStable;decide
theorem columnsPerRow_tableStable : tableStable columnsPerRow := by unfold tableStable entryStable;decide
theorem returnPC_tableStable : tableStable 1 := by unfold tableStable entryStable;decide
theorem outputStart_tableStable : tableStable outputStart := by unfold tableStable entryStable;decide

end PDCompute.Pack
