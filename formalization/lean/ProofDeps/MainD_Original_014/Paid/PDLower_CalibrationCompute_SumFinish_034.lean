module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027
public import Paid.PDLower_CalibrationCompute_Rows_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def sumFinishLeadCode : List Instruction :=
  loadSlot 5 .index ++ loadSlot 9 .old ++ [.natOp .add .address .old .index,.load .value .address,
    .constant .old (.rational (1/2)),.ratOp .multiply .value .value .old] ++
    loadSlot 11 .old ++ [.ratOp .add .value .old .value]

def sumFinishLeadResult (before : State) (base read level : ℕ) (q center : ℚ) : State :=
  let a := loadSlotResult (loadSlotResult before base 5 .index) base 9 .old
  let b := {a with
    pc:=a.pc+4
    register:=Function.update
      (Function.update (Function.update a.register .address (.natural (read+level)))
        .old (.rational (1/2))) .value (.rational (center*(1/2)))}
  let c := loadSlotResult b base 11 .old
  {c with pc:=c.pc+1,register:=Function.update c.register .value (.rational (q+center*(1/2)))}

def sumFinishResult (before : State) (base read level : ℕ) (q center : ℚ) : State :=
  storeSlotResult (sumFinishLeadResult before base read level q center) base 11 .value

theorem sumFinishLead_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (row : Array ℚ) (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.level<row.size) (fresh : before.register .fresh=.natural base) :
    linearExecute input sumFinishLeadCode before =
      some (sumFinishLeadResult before base header.readBase header.level header.q (row.getD header.level 0)) := by
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  have read := represented.lookup (offset:=9) (value:=.natural header.readBase) rfl
  have sum := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have cellLive := rowAt.live header.level inside
  have cellValue := rowAt.value header.level inside
  simp [sumFinishLeadCode,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,RatOp.eval,
    Cell.nat?,Cell.rat?,fresh,level.1,level.2,read.1,read.2,sum.1,sum.2,cellLive,cellValue,
    sumFinishLeadResult,loadSlotResult,Nat.add_assoc]
  funext register
  cases register <;> simp

theorem sumFinish_execute (input : List Cell) (before : State) (base : ℕ) (header : Header)
    (row : Array ℚ) (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.level<row.size) (fresh : before.register .fresh=.natural base) :
    linearExecute input (basicBlock .sumFinish).body before =
      some (sumFinishResult before base header.readBase header.level header.q (row.getD header.level 0)) := by
  have code : (basicBlock .sumFinish).body=sumFinishLeadCode ++ storeSlot 11 .value := by
    simp only [basicBlock,sumFinishLeadCode,List.append_assoc]
  rw [code,linearExecute_append,sumFinishLead_execute input before base header row represented rowAt inside fresh,Option.bind_some]
  exact storeSlot_execute input _ base 11 .value
    (by simpa [sumFinishLeadResult,loadSlotResult] using fresh) (by decide)

theorem sumFinish_header {before : State} {base : ℕ} {header : Header} (row : Array ℚ)
    (represented : header.At before base) :
    ({header with q:=header.q+row.getD header.level 0*(1/2)}).At
      (sumFinishResult before base header.readBase header.level header.q (row.getD header.level 0)) base := by
  have unchanged : header.At (sumFinishLeadResult before base header.readBase header.level header.q
    (row.getD header.level 0)) base := represented
  exact unchanged.storeResult 11 (by decide) .value (.rational (header.q+row.getD header.level 0*(1/2)))
    (by simp [sumFinishLeadResult]) (Header.set_q _ _)

end PDLower.CalibrationCompute
