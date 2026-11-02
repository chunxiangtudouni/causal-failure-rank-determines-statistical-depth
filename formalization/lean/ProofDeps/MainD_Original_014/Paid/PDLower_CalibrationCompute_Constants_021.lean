module

public import Paid.PDLower_CalibrationCompute_Code_003
public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def constantSlotResult (before : State) (base offset : ℕ) (value : Cell) : State :=
  storeSlotResult ({before with pc := before.pc+1}.set .value value) base offset .value

theorem constantSlot_execute (input : List Cell) (before : State) (base offset : ℕ) (value : Cell)
    (fresh : before.register .fresh = .natural base) :
    linearExecute input (constantSlot offset value) before = some (constantSlotResult before base offset value) := by
  simp only [constantSlot,linearExecute_append,linearExecute,Instruction.execute]
  exact storeSlot_execute input _ base offset .value (by simpa [State.set] using fresh) (by decide)

theorem constantSlot_fresh (before : State) (base offset : ℕ) (value : Cell) :
    (constantSlotResult before base offset value).register .fresh = before.register .fresh := by
  simp [constantSlotResult,storeSlotResult,State.set]

theorem constantSlot_heap (before : State) (base offset : ℕ) (value : Cell) :
    (constantSlotResult before base offset value).heap = Function.update before.heap (base+offset) value := by
  simp [constantSlotResult,storeSlotResult,State.set]

theorem constantSlot_live (before : State) (base offset : ℕ) (value : Cell) :
    (constantSlotResult before base offset value).live = insert (base+offset) before.live := rfl

theorem constantSlot_output (before : State) (base offset : ℕ) (value : Cell) :
    (constantSlotResult before base offset value).output = before.output := rfl

theorem constantSlot_pc (before : State) (base offset : ℕ) (value : Cell) :
    (constantSlotResult before base offset value).pc = before.pc+4 := by
  simp [constantSlotResult,storeSlotResult,State.set,Nat.add_assoc]

end PDLower.CalibrationCompute
