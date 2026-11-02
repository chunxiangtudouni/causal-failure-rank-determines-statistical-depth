module

public import Paid.PDLower_CalibrationCompute_Fetch_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- One fixed literal standalone loader. It copies only the original
per-calibration readonly endpoint input; M,Q,gamma stay in their original
argument registers. .fresh is the temporary copy cell until restored to
the fresh workspace address. No hidden derived cache or trace is input. -/
def bootstrap (origin : ℕ) : Program := #[
  .constant .address (.natural 0),
  .loadInput .total .address,
  .constant .address (.natural 1),
  .loadInput .index .address,
  .constant .address (.natural 2),
  .loadInput .value .address,
  .constant .old (.natural 2),
  .natOp .multiply .flag .total .old,
  .constant .old (.natural 3),
  .natOp .add .flag .flag .old,
  .constant .address (.natural 0),
  .constant .old (.natural 3),
  .branchZero .flag (origin+20) (origin+13),
  .loadInput .fresh .old,
  .store .address .fresh,
  .constant .fresh (.natural 1),
  .natOp .add .old .old .fresh,
  .natOp .add .address .address .fresh,
  .natOp .subtract .flag .flag .fresh,
  .jump (origin+12),
  .constant .old (.natural 2),
  .natOp .multiply .fresh .total .old,
  .constant .old (.natural 3),
  .natOp .add .fresh .fresh .old,
  .constant .address (.natural 0),
  .constant .old (.natural (origin+27)),
  .jump 1,
  .halt]

theorem bootstrap_size (origin : ℕ) : (bootstrap origin).size = 28 := rfl

def mainStart : ℕ := 1+(kernel 1).size

/-- Chosen BEFORE every paper input. Both core and this standalone program
can contain the identical kernel at origin1. Initial pc0 skips the callee;
only the genuine endpoint-load completion calls it. -/
def calibrate : Program := #[.jump mainStart] ++ kernel 1 ++ bootstrap mainStart

theorem initial_jump_fetch : calibrate[0]? = some (.jump mainStart) := by
  have singleton : (#[Instruction.jump mainStart] : Program).size = 1 := rfl
  unfold calibrate
  rw [Array.getElem?_append_left (by simp only [Array.size_append,singleton]; omega),
    Array.getElem?_append_left (by decide)]
  rfl

theorem calibrate_kernel_fetch (offset : ℕ) (inside : offset < (kernel 1).size) :
    calibrate[1+offset]? = (kernel 1)[offset]? := by
  exact PDMenu.ComputeFrame.appendBlock_fetch #[.jump mainStart] (kernel 1) (bootstrap mainStart) offset inside

theorem calibrate_bootstrap_fetch (offset : ℕ) :
    calibrate[mainStart+offset]? = (bootstrap mainStart)[offset]? := by
  have length : ((#[Instruction.jump mainStart] : Program) ++ kernel 1).size = mainStart := by
    have singleton : (#[Instruction.jump mainStart] : Program).size = 1 := rfl
    rw [Array.size_append,singleton]
    unfold mainStart
    rfl
  unfold calibrate
  rw [Array.getElem?_append_right (by rw [length]; omega),length,Nat.add_sub_cancel_left]

theorem calibrate_halt_fetch : calibrate[mainStart+27]? = some .halt := by
  rw [calibrate_bootstrap_fetch]
  rfl

theorem calibrate_call_fetch : calibrate[mainStart+26]? = some (.jump 1) := by
  rw [calibrate_bootstrap_fetch]
  rfl

theorem calibrate_size : calibrate.size = mainStart+28 := by
  have singleton : (#[Instruction.jump mainStart] : Program).size = 1 := rfl
  simp only [calibrate,Array.size_append,bootstrap_size,singleton]
  unfold mainStart
  rfl

end PDLower.CalibrationCompute
