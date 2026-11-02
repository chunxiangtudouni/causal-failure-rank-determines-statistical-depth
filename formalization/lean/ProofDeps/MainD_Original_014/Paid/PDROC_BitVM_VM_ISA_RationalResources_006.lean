module

public import Paid.PDROC_BitVM_VM_ISA_RationalRefinement_005
public import Paid.PDROC_BitVM_Kernel_RatCompareBudget_059

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

theorem rat_resources (backend : RatBackend) (core : Bool) (operation : RatOp) (target left right : Register) :
    ResourceRefinement backend core ⟨.ratOp operation target left right,rfl⟩ := by
  let C := Kernel.RawInstruction.resourceCoefficient (backend.machine operation) left right (backend.c operation) (backend.d operation)
  refine ⟨C,backend.d operation,Kernel.RawInstruction.resourceCoefficient_positive _ _ _ _ _,
    (backend.valid operation).2.1,?_⟩
  intro input logical next events contents _size ready success
  obtain ⟨x,y,result,leftRat,rightRat,evaluated,same⟩ := rat_operands input logical next operation target left right success
  subst next
  obtain ⟨run,final,_original,head,chain,last,halt,_registers,_work0,_work24,_work25,_work29,time,_frame⟩ :=
    Kernel.RawInstruction.instruction_runs (backend.machine operation) operation
      (Kernel.RawInstruction.resultFunction operation) (backend.c operation) (backend.d operation)
      (backend.valid operation).2.2.1 (backend.valid operation).2.2.2 input logical target left right
      x y result contents ready.registers leftRat rightRat evaluated
      (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
  refine ⟨run,final,⟨head,chain,last,halt⟩,time.trans ?_⟩
  have localBound := Kernel.RawInstruction.budget_polynomial (backend.machine operation) logical left right x y
    (backend.c operation) (backend.d operation) (backend.valid operation).2.1 contents ready.registers leftRat rightRat
  apply localBound.trans
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left
    (by omega : Kernel.NatInstruction.dataSize contents+1 ≤
      Kernel.NatInstruction.dataSize contents+(encodeBits input).length+1) (backend.d operation))

theorem rat_compare_resources (backend : RatBackend) (core : Bool) (comparison : Comparison) (target left right : Register) :
    ResourceRefinement backend core ⟨.ratCompare comparison target left right,rfl⟩ := by
  let C := Kernel.RatCompare.resourceCoefficient (backend.machine .subtract) target left right (backend.c .subtract) (backend.d .subtract)
  refine ⟨C,backend.d .subtract,Kernel.RatCompare.resourceCoefficient_positive _ _ _ _ _ _,
    (backend.valid .subtract).2.1,?_⟩
  intro input logical next events contents _size ready success
  obtain ⟨x,y,leftRat,rightRat,same⟩ := compare_operands input logical next comparison target left right success
  subst next
  obtain ⟨run,final,_original,head,chain,last,halt,_registers,_work0,_work24,_work25,_work29,time,_frame⟩ :=
    Kernel.RatCompare.instruction_runs (backend.machine .subtract) comparison (backend.c .subtract) (backend.d .subtract)
      (backend.valid .subtract).2.2.1 input logical target left right x y contents ready.registers leftRat rightRat
      (ready.workspace 0 (Or.inl rfl)) (ready.workspace 24 (Or.inr (by decide)))
  refine ⟨run,final,⟨head,chain,last,halt⟩,time.trans ?_⟩
  have localBound := Kernel.RatCompare.budget_polynomial (backend.machine .subtract) logical target left right x y
    (backend.c .subtract) (backend.d .subtract) (backend.valid .subtract).2.1 contents ready.registers leftRat rightRat
  apply localBound.trans
  exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left
    (by omega : Kernel.NatInstruction.dataSize contents+1 ≤
      Kernel.NatInstruction.dataSize contents+(encodeBits input).length+1) (backend.d .subtract))

end PDROC.BitVM.VM.ISA
