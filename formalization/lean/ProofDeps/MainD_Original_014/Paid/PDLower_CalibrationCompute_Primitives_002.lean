module

public import Paid.PDLower_CalibrationCompute_ABI_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- Straight-line expansion of actual literal ISA instructions. It is
used only with a separate genuine program-fetch/trace refinement. -/
def linearExecute (input : List Cell) : List Instruction → State → Option State
  | [],state => some state
  | instruction::rest,state => (instruction.execute input state).bind (linearExecute input rest)

def storeSlot (offset : ℕ) (source : Register) : List Instruction :=
  [.constant .address (.natural offset),.natOp .add .address .fresh .address,.store .address source]

def loadSlot (offset : ℕ) (target : Register) : List Instruction :=
  [.constant .address (.natural offset),.natOp .add .address .fresh .address,.load target .address]

def storeSlotResult (state : State) (base offset : ℕ) (source : Register) : State :=
  { state with
    register := Function.update state.register .address (.natural (base+offset))
    heap := Function.update state.heap (base+offset) (state.register source)
    live := insert (base+offset) state.live
    pc := state.pc+3 }

theorem storeSlot_execute (input : List Cell) (state : State) (base offset : ℕ) (source : Register)
    (baseValue : state.register .fresh = .natural base) (safe : source ≠ .address) :
    linearExecute input (storeSlot offset source) state = some (storeSlotResult state base offset source) := by
  simp [linearExecute,storeSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,baseValue,
    safe,storeSlotResult,Nat.add_assoc]

theorem storeSlot_frame (state : State) (base offset : ℕ) (source : Register) (M : ℕ)
    (inside : offset < workspaceSize M) : Frame state (storeSlotResult state base offset source) base M := by
  have member : base+offset ∈ workspace base M := Finset.mem_image.mpr ⟨offset,Finset.mem_range.mpr inside,rfl⟩
  constructor
  · intro address outside
    have different : address ≠ base+offset := by intro eq; subst address; exact outside member
    simp only [storeSlotResult,Function.update_apply]
    rw [ite_eq_right different]
  · intro address outside
    have different : address ≠ base+offset := by intro eq; subst address; exact outside member
    simp only [storeSlotResult,Finset.mem_insert,different,false_or]

/-- Save the real caller return address, endpoint heap address, M,Q,gamma.
No parameter-dependent constant appears in the literal program. -/
def prologue : List Instruction :=
  [.move .flag .address] ++ storeSlot 0 .old ++ storeSlot 1 .flag ++
    storeSlot 2 .total ++ storeSlot 3 .index ++ storeSlot 4 .value

theorem prologue_length : prologue.length = 16 := rfl

end PDLower.CalibrationCompute
