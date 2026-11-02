module

public import Paid.PDLower_CalibrationCompute_Increment_028
public import Paid.PDLower_CalibrationCompute_SumValue_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def sumCellLeadCode : List Instruction :=
  loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address] ++
    loadSlot 11 .old ++ [.ratOp .add .value .old .value]

def sumCellLeadResult (before : State) (base read cursor : ℕ) (q value : ℚ) : State :=
  let a := loadSlotResult before base 9 .old
  let b := {a with
    pc := a.pc+2
    register := Function.update (Function.update a.register .address (.natural (read+cursor)))
      .value (.rational value)}
  let c := loadSlotResult b base 11 .old
  {c with pc := c.pc+1,register := Function.update c.register .value (.rational (q+value))}

def sumCellResult (before : State) (base read cursor : ℕ) (q value : ℚ) : State :=
  incrementSlotResult (storeSlotResult (sumCellLeadResult before base read cursor q value) base 11 .value)
    base 7 cursor

theorem sumCellLead_execute (input : List Cell) (before : State) (base read cursor : ℕ) (q value : ℚ)
    (fresh : before.register .fresh = .natural base) (index : before.register .index = .natural cursor)
    (readLive : base+9 ∈ before.live) (readValue : before.heap (base+9) = .natural read)
    (sumLive : base+11 ∈ before.live) (sumValue : before.heap (base+11) = .rational q)
    (cellLive : read+cursor ∈ before.live) (cellValue : before.heap (read+cursor) = .rational value) :
    linearExecute input sumCellLeadCode before = some (sumCellLeadResult before base read cursor q value) := by
  simp [sumCellLeadCode,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,RatOp.eval,
    Cell.nat?,Cell.rat?,fresh,index,readLive,readValue,sumLive,sumValue,cellLive,cellValue,
    sumCellLeadResult,loadSlotResult,Nat.add_assoc]

/-- One REAL scalar summation iteration: row read, rational addition,
header write and actual cursor increment. It accepts no iteration result. -/
theorem sumCell_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (row : Array ℚ) (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.cursor < row.size)
    (fresh : before.register .fresh = .natural base)
    (index : before.register .index = .natural header.cursor) :
    linearExecute input (basicBlock .sumCell).body before =
      some (sumCellResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)) := by
  have read := represented.lookup (offset := 9) (value := .natural header.readBase) rfl
  have sum := represented.lookup (offset := 11) (value := .rational header.q) rfl
  have cursor := represented.lookup (offset := 7) (value := .natural header.cursor) rfl
  let d := sumCellLeadResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)
  let e := storeSlotResult d base 11 .value
  have fd : d.register .fresh = .natural base := by simpa [d,sumCellLeadResult,loadSlotResult] using fresh
  have fe : e.register .fresh = .natural base := by simpa [e,storeSlotResult] using fd
  have ce : base+7 ∈ e.live := Finset.mem_insert_of_mem cursor.2
  have ve : e.heap (base+7) = .natural header.cursor := by
    simpa [e,d,storeSlotResult,sumCellLeadResult,loadSlotResult] using cursor.1
  have code : (basicBlock .sumCell).body = sumCellLeadCode ++ storeSlot 11 .value ++ incrementSlot 7 := by
    simp only [basicBlock,sumCellLeadCode,List.append_assoc]
  change linearExecute input (basicBlock .sumCell).body before = some (incrementSlotResult e base 7 header.cursor)
  rw [code,List.append_assoc,linearExecute_append,sumCellLead_execute input before base header.readBase header.cursor header.q
    (row.getD header.cursor 0) fresh index read.2 read.1 sum.2 sum.1 (rowAt.live _ inside)
    (rowAt.value _ inside),Option.bind_some]
  rw [linearExecute_append,storeSlot_execute input d base 11 .value fd (by decide),Option.bind_some]
  exact incrementSlot_execute input e base 7 header.cursor fe ce ve

theorem sumCell_header {before : State} {base : ℕ} {header : Header} (row : Array ℚ)
    (represented : header.At before base) :
    ({header with q := header.q+row.getD header.cursor 0,cursor := header.cursor+1}).At
      (sumCellResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)) base := by
  let d := sumCellLeadResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)
  have unchanged : header.At d base := represented
  have sumHeader : ({header with q := header.q+row.getD header.cursor 0}).At (storeSlotResult d base 11 .value) base :=
    unchanged.storeResult 11 (by decide) .value (.rational (header.q+row.getD header.cursor 0))
      (by simp [d,sumCellLeadResult]) (Header.set_q _ _)
  exact incrementSlot_header sumHeader (by decide) (Header.set_cursor _ _)

end PDLower.CalibrationCompute
