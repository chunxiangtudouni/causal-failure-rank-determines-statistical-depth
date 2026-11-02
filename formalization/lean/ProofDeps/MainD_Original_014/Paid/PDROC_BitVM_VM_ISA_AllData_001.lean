module

public import Paid.PDROC_BitVM_VM_ISA_ConstantRefinement_007
public import Paid.PDROC_BitVM_VM_ISA_MoveRefinement_001
public import Paid.PDROC_BitVM_VM_ISA_NaturalRefinement_002
public import Paid.PDROC_BitVM_VM_ISA_RationalResources_006
public import Paid.PDROC_BitVM_VM_ISA_HeapRefinement_002
public import Paid.PDROC_BitVM_VM_ISA_HeapResources_002
public import Paid.PDROC_BitVM_VM_ISA_CodecRefinement_004
public import Paid.PDROC_BitVM_VM_ISA_CodecResources_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.AllData

open Turing PaperProofs.Paid.Computation

/-- Static exhaustive original data syntax. No runtime dispatch, cell
value, source RAM state or successful-run oracle is a machine field.
Control cases are excluded by the ORIGINAL DataInstruction predicate. -/
theorem semantic (backend : RatBackend) (core : Bool) (data : DataInstruction) :
    StepRefinement backend core data := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant target value => exact constant_step backend core target value
  | move target source => exact MoveRefinement.move_step backend core target source
  | loadInput destination pointer => exact HeapRefinement.inputLoad_step backend core destination pointer
  | load destination pointer => exact HeapRefinement.load_step backend core destination pointer
  | store pointer source => exact HeapRefinement.store_step backend core pointer source
  | release pointer => exact HeapRefinement.release_step backend core pointer
  | natOp operation target left right => exact NaturalRefinement.natural_step backend core operation target left right
  | ratOp operation target left right => exact rat_step backend core operation target left right
  | natCompare comparison target left right => exact CodecRefinement.natCompare_step backend core comparison target left right
  | ratCompare comparison target left right => exact rat_compare_step backend core comparison target left right
  | natToRat target source => exact CodecRefinement.natCast_step backend core target source
  | numeratorAbs target source => exact CodecRefinement.numeratorAbs_step backend core target source
  | denominator target source => exact CodecRefinement.denominator_step backend core target source
  | negative target source => exact CodecRefinement.negative_step backend core target source
  | output source => exact CodecRefinement.output_step backend core source
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

/-- The old quantitative resource implementations, with every C,D
chosen before all actual data, are aggregated without rebuilding paths. -/
theorem resource (backend : RatBackend) (core : Bool) (data : DataInstruction) :
    ResourceRefinement backend core data := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant target value => exact constant_resources backend core target value
  | move target source => exact MoveRefinement.move_resource backend core target source
  | loadInput destination pointer => exact HeapResources.inputLoad_resource backend core destination pointer
  | load destination pointer => exact HeapResources.load_resource backend core destination pointer
  | store pointer source => exact HeapResources.store_resource backend core pointer source
  | release pointer => exact HeapResources.release_resource backend core pointer
  | natOp operation target left right => exact NaturalRefinement.natural_resource backend core operation target left right
  | ratOp operation target left right => exact rat_resources backend core operation target left right
  | natCompare comparison target left right => exact CodecResources.natCompare_resource backend core comparison target left right
  | ratCompare comparison target left right => exact rat_compare_resources backend core comparison target left right
  | natToRat target source => exact CodecResources.natCast_resource backend core target source
  | numeratorAbs target source => exact CodecResources.numeratorAbs_resource backend core target source
  | denominator target source => exact CodecResources.denominator_resource backend core target source
  | negative target source => exact CodecResources.negative_resource backend core target source
  | output source => exact CodecResources.output_resource backend core source
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

/-- Complete shared contract on ONE actual directory macro trace.
Spec003 uses RootTrace038 whole halting-run uniqueness to identify the
semantic and resource witnesses. No two unrelated paths are concatenated. -/
theorem complete (backend : RatBackend) (core : Bool) (data : DataInstruction) :
    ∃ C D : ℕ, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Source.Ready input logical events contents →
        Instruction.execute input data.val logical = some next →
        ∃ (run : List (State backend data)) (final : State backend data),
          ActualRun backend core data contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf data.val logical).toList) final.stk ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D :=
  combine_refinements backend core data (semantic backend core data) (resource backend core data)

end PDROC.BitVM.VM.ISA.AllData
