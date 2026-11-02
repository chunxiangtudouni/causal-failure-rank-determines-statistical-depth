module

public import Paid.PDROC_BitVM_VM_ISA_CodecResources_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecResources

open Turing PaperProofs.Paid.Computation

/-- The coefficient is chosen BEFORE all inputs. Only represented Nat
operand BIT lengths are bounded; arbitrary old physical data remain in
the actual32-stack size. No value-square, B, fuel or workspace oracle. -/
theorem natCompare_resource (backend : RatBackend) (core : Bool) (comparison : Comparison)
    (target left right : Register) :
    ResourceRefinement backend core ⟨.natCompare comparison target left right, rfl⟩ := by
  refine ⟨comparisonCoefficient left right, 2, comparisonCoefficient_pos left right, by decide, ?_⟩
  intro input logical next events contents _size ready success
  cases leftValue : logical.register left with
  | rational q => simp [Instruction.execute, leftValue, Cell.nat?] at success
  | natural a =>
    cases rightValue : logical.register right with
    | rational q => simp [Instruction.execute, leftValue, rightValue, Cell.nat?] at success
    | natural b =>
      obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
        _work0, _work24, _work25, _work26, _frame, time, _space⟩ :=
        Codec.NatCompare.instruction_runs input comparison target left right logical a b contents
          Codec.NatCompare.clearedStore ready.registers leftValue rightValue
      have ha := nat_bits_le logical contents left a ready.registers leftValue
      have hb := nat_bits_le logical contents right b ready.registers rightValue
      have quadratic := time.trans (comparison_quadratic left right contents a b ha hb)
      have size : (Kernel.NatInstruction.dataSize contents + 1)^2 ≤
          (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^2 :=
        Nat.pow_le_pow_left (by omega) 2
      refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
      exact quadratic.trans (Nat.mul_le_mul_left (comparisonCoefficient left right) size)

end PDROC.BitVM.VM.ISA.CodecResources
