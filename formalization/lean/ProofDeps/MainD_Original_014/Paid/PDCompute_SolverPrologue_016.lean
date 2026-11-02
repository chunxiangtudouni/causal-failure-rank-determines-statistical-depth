module

public import Paid.PDCompute_SolverBaseRowComplete_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute storeSlot storeSlotResult writeCell)

/-- Preserve the actual endpoint source FIRST: the shared storeSlot macro
uses .address as scratch, while all seven input registers already hold
real arguments. No input-dependent constant is inserted into this code. -/
def solverPrologue : List Instruction :=
  [.store .fresh .address]++storeSlot 1 .old++storeSlot 2 .total++storeSlot 3 .index++
    storeSlot 4 .value++storeSlot 5 .flag

def solverPrologueResult (before : State) (base : ℕ) : State :=
  let zero := writeCell before base (before.register .address)
  let one := storeSlotResult zero base 1 .old
  let two := storeSlotResult one base 2 .total
  let three := storeSlotResult two base 3 .index
  let four := storeSlotResult three base 4 .value
  storeSlotResult four base 5 .flag

theorem solverPrologue_length : solverPrologue.length=16 := rfl

theorem solverPrologue_execute (input : List Cell) (before : State) (base : ℕ)
    (hbase : before.register .fresh=.natural base) :
    linearExecute input solverPrologue before=some (solverPrologueResult before base) := by
  simp [linearExecute,solverPrologue,storeSlot,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
    hbase,solverPrologueResult,storeSlotResult,writeCell,Nat.add_assoc]

theorem solverPrologue_pc (before : State) (base : ℕ) : (solverPrologueResult before base).pc=before.pc+16 := by
  simp only [solverPrologueResult,storeSlotResult,writeCell]

theorem solverPrologue_output (before : State) (base : ℕ) :
    (solverPrologueResult before base).output=before.output := rfl

theorem solverPrologue_base (before : State) (base : ℕ) :
    (solverPrologueResult before base).register .fresh=before.register .fresh := by
  simp [solverPrologueResult,storeSlotResult,writeCell]

theorem solverPrologue_frame (before : State) (base n k : ℕ) :
    Frame before (solverPrologueResult before base) base n k := by
  have avoid (address : ℕ) (hout : address ∉ workspace base n k) (offset : ℕ) (hoff : offset < 6) :
      address ≠ base+offset := by
    intro he
    apply hout
    rw [he]
    apply Finset.mem_image.mpr
    refine ⟨offset,Finset.mem_range.mpr ?_,rfl⟩
    unfold workspaceSize headerWords
    omega
  constructor
  · intro address hout
    have hz : address ≠ base := by simpa only [Nat.add_zero] using avoid address hout 0 (by omega)
    simp only [solverPrologueResult,storeSlotResult,writeCell,Function.update_apply,
      avoid address hout 5 (by omega),avoid address hout 4 (by omega),avoid address hout 3 (by omega),
      avoid address hout 2 (by omega),avoid address hout 1 (by omega),hz,↓reduceIte]
  · intro address hout
    have hz : address ≠ base := by simpa only [Nat.add_zero] using avoid address hout 0 (by omega)
    simp only [solverPrologueResult,storeSlotResult,writeCell,Finset.mem_insert,
      avoid address hout 5 (by omega),avoid address hout 4 (by omega),avoid address hout 3 (by omega),
      avoid address hout 2 (by omega),avoid address hout 1 (by omega),hz,false_or]

end PDCompute.Solver
