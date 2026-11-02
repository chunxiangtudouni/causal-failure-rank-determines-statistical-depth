module

public import Paid.PDLower_CalibrationCompute_Primitives_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem linearExecute_append (input : List Cell) (first later : List Instruction) (state : State) :
    linearExecute input (first++later) state =
      (linearExecute input first state).bind (linearExecute input later) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append,linearExecute,ih,Option.bind_assoc]

def loadSlotResult (state : State) (base offset : ℕ) (target : Register) : State :=
  { state with
    register := Function.update (Function.update state.register .address (.natural (base+offset)))
      target (state.heap (base+offset))
    pc := state.pc+3 }

theorem loadSlot_execute (input : List Cell) (state : State) (base offset : ℕ) (target : Register)
    (baseValue : state.register .fresh = .natural base) (live : base+offset ∈ state.live) :
    linearExecute input (loadSlot offset target) state = some (loadSlotResult state base offset target) := by
  simp [linearExecute,loadSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,baseValue,
    live,loadSlotResult,Nat.add_assoc]

theorem loadSlot_heap (state : State) (base offset : ℕ) (target : Register) :
    (loadSlotResult state base offset target).heap = state.heap := rfl

theorem loadSlot_live (state : State) (base offset : ℕ) (target : Register) :
    (loadSlotResult state base offset target).live = state.live := rfl

end PDLower.CalibrationCompute
