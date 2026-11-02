module

public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

theorem Frame.trans {first middle last : State} {base M : ℕ}
    (earlier : Frame first middle base M) (later : Frame middle last base M) : Frame first last base M := by
  constructor
  · intro address outside
    exact (later.1 address outside).trans (earlier.1 address outside)
  · intro address outside
    exact (later.2 address outside).trans (earlier.2 address outside)

def prologueResult (state : State) (base : ℕ) : State :=
  let moved := ({state with pc := state.pc+1}).set .flag (state.register .address)
  let one := storeSlotResult moved base 0 .old
  let two := storeSlotResult one base 1 .flag
  let three := storeSlotResult two base 2 .total
  let four := storeSlotResult three base 3 .index
  storeSlotResult four base 4 .value

theorem prologue_execute (input : List Cell) (state : State) (base : ℕ)
    (baseValue : state.register .fresh = .natural base) :
    linearExecute input prologue state = some (prologueResult state base) := by
  simp [prologue,linearExecute,storeSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,baseValue,
    prologueResult,storeSlotResult,Nat.add_assoc]

theorem prologue_pc (state : State) (base : ℕ) : (prologueResult state base).pc = state.pc+16 := by
  simp only [prologueResult,storeSlotResult,State.set]

theorem prologue_output (state : State) (base : ℕ) : (prologueResult state base).output = state.output := rfl

theorem prologue_base (state : State) (base : ℕ) :
    (prologueResult state base).register .fresh = state.register .fresh := by
  simp [prologueResult,storeSlotResult,State.set]

theorem prologue_frame (state : State) (base M : ℕ) : Frame state (prologueResult state base) base M := by
  have avoid (address : ℕ) (outside : address ∉ workspace base M) (offset : ℕ) (bound : offset < 5) :
      address ≠ base+offset := by
    intro eq
    apply outside
    rw [eq]
    apply Finset.mem_image.mpr
    refine ⟨offset,Finset.mem_range.mpr ?_,rfl⟩
    rw [workspaceSize_linear]
    omega
  constructor
  · intro address outside
    simp only [prologueResult,storeSlotResult,State.set,Function.update_apply,
      avoid address outside 0 (by omega),avoid address outside 1 (by omega),
      avoid address outside 2 (by omega),avoid address outside 3 (by omega),
      avoid address outside 4 (by omega),↓reduceIte]
  · intro address outside
    simp only [prologueResult,storeSlotResult,State.set,Finset.mem_insert,
      avoid address outside 0 (by omega),avoid address outside 1 (by omega),
      avoid address outside 2 (by omega),avoid address outside 3 (by omega),
      avoid address outside 4 (by omega),false_or]

end PDLower.CalibrationCompute
