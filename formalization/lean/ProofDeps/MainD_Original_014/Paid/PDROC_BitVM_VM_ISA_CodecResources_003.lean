module

public import Paid.PDROC_BitVM_VM_ISA_CodecResources_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.CodecResources

open Turing PaperProofs.Paid.Computation

/-- Uniform constants are outside all logical/physical input quantifiers.
This keeps the exact old actual natToRat path and only widens its length. -/
theorem natCast_resource (backend : RatBackend) (core : Bool) (target source : Register) :
    ResourceRefinement backend core ⟨.natToRat target source, rfl⟩ := by
  refine ⟨512, 2, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | rational q => simp [Instruction.execute, sourceValue, Cell.nat?] at success
  | natural value =>
    obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
      _work0, _work24, _work25, _work26, _frame, time, _space⟩ :=
      Codec.NatCast.instruction_runs input target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    change run.length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1) at time
    exact ⟨run, final, ⟨head, chain, last, halt⟩, linear_quadratic input contents run.length time⟩

theorem numeratorAbs_resource (backend : RatBackend) (core : Bool) (target source : Register) :
    ResourceRefinement backend core ⟨.numeratorAbs target source, rfl⟩ := by
  refine ⟨512, 2, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
      _work0, _work24, _work25, _work26, _frame, time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .numeratorAbs target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    change run.length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1) at time
    exact ⟨run, final, ⟨head, chain, last, halt⟩, linear_quadratic input contents run.length time⟩

theorem denominator_resource (backend : RatBackend) (core : Bool) (target source : Register) :
    ResourceRefinement backend core ⟨.denominator target source, rfl⟩ := by
  refine ⟨512, 2, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
      _work0, _work24, _work25, _work26, _frame, time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .denominator target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    change run.length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1) at time
    exact ⟨run, final, ⟨head, chain, last, halt⟩, linear_quadratic input contents run.length time⟩

theorem negative_resource (backend : RatBackend) (core : Bool) (target source : Register) :
    ResourceRefinement backend core ⟨.negative target source, rfl⟩ := by
  refine ⟨512, 2, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready success
  cases sourceValue : logical.register source with
  | natural n => simp [Instruction.execute, sourceValue, Cell.rat?] at success
  | rational value =>
    obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
      _work0, _work24, _work25, _work26, _frame, time, _space⟩ :=
      Codec.FieldOps.instruction_runs input .negative target source logical value contents Codec.FieldOps.clearedStore
        ready.registers sourceValue
    change run.length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1) at time
    exact ⟨run, final, ⟨head, chain, last, halt⟩, linear_quadratic input contents run.length time⟩

/-- Actual complete Cell emit/tick/clear already has a stronger32(g+1)
clock bound. It is widened numerically, not replaced with another path. -/
theorem output_resource (backend : RatBackend) (core : Bool) (source : Register) :
    ResourceRefinement backend core ⟨.output source, rfl⟩ := by
  refine ⟨512, 2, by decide, by decide, ?_⟩
  intro input logical next events contents _size ready _success
  obtain ⟨run, final, _executed, head, chain, last, halt, _store, _registers,
    _work0, _work24, _word, _ticks, _frame, time, _space⟩ :=
    Codec.OutputInstruction.instruction_runs input logical source contents Codec.OutputInstruction.clearedStore
      ready.registers ready.outputWord ready.outputTicks
  change run.length ≤ 32 * (Kernel.NatInstruction.dataSize contents + 1) at time
  have widened : run.length ≤ 512 * (Kernel.NatInstruction.dataSize contents + 1) :=
    time.trans (Nat.mul_le_mul_right _ (by decide : 32 ≤ 512))
  exact ⟨run, final, ⟨head, chain, last, halt⟩, linear_quadratic input contents run.length widened⟩

end PDROC.BitVM.VM.ISA.CodecResources
