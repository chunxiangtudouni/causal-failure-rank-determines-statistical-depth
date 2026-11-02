module

public import Paid.PDLower_CalibrationCompute_Linear_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

structure RowAt (state : State) (base : ℕ) (row : Array ℚ) : Prop where
  live : ∀ i < row.size,base+i ∈ state.live
  value : ∀ i < row.size,state.heap (base+i) = .rational (row.getD i 0)

def writeCell (state : State) (address : ℕ) (value : Cell) : State :=
  { state with
    heap := Function.update state.heap address value
    live := insert address state.live
    pc := state.pc+1 }

theorem writeCell_execute (input : List Cell) (state : State) (address : ℕ) (value : Cell)
    (pointer : state.register .address = .natural address) (stored : state.register .value = value) :
    Instruction.execute input (.store .address .value) state = some (writeCell state address value) := by
  simp [Instruction.execute,pointer,stored,Cell.nat?,writeCell]

theorem RowAt.bump (state : State) (base : ℕ) (row : Array ℚ) (represented : RowAt state base row)
    (index : ℕ) (bound : index < row.size) (amount : ℚ) :
    RowAt (writeCell state (base+index) (.rational (row.getD index 0+amount))) base
      (PDROC.endpointArrayBump row index amount) := by
  constructor
  · intro i inside
    rw [PDROC.endpointArrayBump_size] at inside
    exact Finset.mem_insert_of_mem (represented.live i inside)
  · intro i inside
    rw [PDROC.endpointArrayBump_size] at inside
    simp only [writeCell,Function.update_apply]
    rw [PDROC.endpointArrayBump_getD row index i amount bound]
    by_cases same : index = i
    · subst i
      simp
    · have different : base+i ≠ base+index := by
        intro eq
        exact same (Nat.add_left_cancel eq).symm
      rw [ite_eq_right different,represented.value i inside,ite_eq_right same,add_zero]

theorem RowAt.writeOutside (state : State) (base : ℕ) (row : Array ℚ) (represented : RowAt state base row)
    (address : ℕ) (value : Cell) (separate : ∀ i < row.size,address ≠ base+i) :
    RowAt (writeCell state address value) base row := by
  constructor
  · intro i inside
    exact Finset.mem_insert_of_mem (represented.live i inside)
  · intro i inside
    simp only [writeCell,Function.update_apply]
    rw [ite_eq_right (Ne.symm (separate i inside))]
    exact represented.value i inside

end PDLower.CalibrationCompute
