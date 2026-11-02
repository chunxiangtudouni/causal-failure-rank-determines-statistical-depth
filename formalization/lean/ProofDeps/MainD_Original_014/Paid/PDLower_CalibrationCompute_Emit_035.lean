module

public import Paid.PDLower_CalibrationCompute_Increment_028

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def emitLeadCode : List Instruction :=
  loadSlot 15 .index ++ loadSlot 11 .old ++ [.store .index .old,.constant .flag (.natural 1),
    .natOp .add .index .index .flag,.store .index .value,.output .old,.output .value,
    .natOp .add .index .index .flag]

def emitLeadResult (before : State) (base cursor : ℕ) (q weight : ℚ) : State :=
  let loaded := loadSlotResult (loadSlotResult before base 15 .index) base 11 .old
  {loaded with
    pc:=loaded.pc+7
    register:=Function.update (Function.update loaded.register .flag (.natural 1))
      .index (.natural (cursor+2)),
    heap:=Function.update (Function.update loaded.heap cursor (.rational q)) (cursor+1) (.rational weight),
    live:=insert (cursor+1) (insert cursor loaded.live),
    output:=loaded.output++[.rational q,.rational weight]}

def emitResult (before : State) (base cursor level : ℕ) (q weight : ℚ) : State :=
  incrementSlotResult (storeSlotResult (emitLeadResult before base cursor q weight) base 15 .index) base 5 level

/-- The real two stores AND the real two stream emissions occur here;
updating only a mathematical cache would not establish this lemma. -/
theorem emitLead_execute (input : List Cell) (before : State) (base cursor : ℕ) (q weight : ℚ)
    (fresh : before.register .fresh=.natural base) (value : before.register .value=.rational weight)
    (cursorLive : base+15 ∈ before.live) (cursorValue : before.heap (base+15)=.natural cursor)
    (qLive : base+11 ∈ before.live) (qValue : before.heap (base+11)=.rational q) :
    linearExecute input emitLeadCode before = some (emitLeadResult before base cursor q weight) := by
  simp [emitLeadCode,linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    fresh,value,cursorLive,cursorValue,qLive,qValue,emitLeadResult,loadSlotResult,Nat.add_assoc,List.append_assoc]

theorem emit_execute (input : List Cell) (before : State) (base : ℕ) (header : Header) (weight : ℚ)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (value : before.register .value=.rational weight)
    (cursorOutside : base+16 ≤ header.outputCursor) :
    linearExecute input (basicBlock .emit).body before =
      some (emitResult before base header.outputCursor header.level header.q weight) := by
  have cursor := represented.lookup (offset:=15) (value:=.natural header.outputCursor) rfl
  have q := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have level := represented.lookup (offset:=5) (value:=.natural header.level) rfl
  let d := emitLeadResult before base header.outputCursor header.q weight
  let e := storeSlotResult d base 15 .index
  have fd : d.register .fresh=.natural base := by simpa [d,emitLeadResult,loadSlotResult] using fresh
  have fe : e.register .fresh=.natural base := by simpa [e,storeSlotResult] using fd
  have live : base+5 ∈ e.live :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem level.2))
  have correct : e.heap (base+5)=.natural header.level := by
    have h0 : base+5 ≠ header.outputCursor := by omega
    have h1 : base+5 ≠ header.outputCursor+1 := by omega
    simpa [e,d,storeSlotResult,emitLeadResult,loadSlotResult,h0,h1] using level.1
  have code : (basicBlock .emit).body=emitLeadCode ++ storeSlot 15 .index ++ incrementSlot 5 := by
    simp only [basicBlock,emitLeadCode,List.append_assoc]
  change linearExecute input (basicBlock .emit).body before = some (incrementSlotResult e base 5 header.level)
  rw [code,List.append_assoc,linearExecute_append,emitLead_execute input before base header.outputCursor header.q weight
    fresh value cursor.2 cursor.1 q.2 q.1,Option.bind_some]
  rw [linearExecute_append,storeSlot_execute input d base 15 .index fd (by decide),Option.bind_some]
  exact incrementSlot_execute input e base 5 header.level fe live correct

theorem emit_output (before : State) (base cursor level : ℕ) (q weight : ℚ) :
    (emitResult before base cursor level q weight).output = before.output++[.rational q,.rational weight] := rfl

end PDLower.CalibrationCompute
