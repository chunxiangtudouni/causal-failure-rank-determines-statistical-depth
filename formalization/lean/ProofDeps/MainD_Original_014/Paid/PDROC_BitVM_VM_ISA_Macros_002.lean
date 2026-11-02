module

public import Paid.PDROC_BitVM_VM_ISA_Types_001
public import Paid.PDROC_BitVM_VM_Control_Indirect_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

def moveStart (source target : Register) : moveLabel source target := by
  unfold moveLabel
  split_ifs
  · exact ()
  · exact 0

def moveInitial (source target : Register) : moveStore source target := by
  unfold moveStore
  split_ifs
  · exact ()
  · exact (none, ())

def moveProgram (source target : Register) :
    moveLabel source target → TM2.Stmt Alphabet (moveLabel source target) (moveStore source target) :=
  if h : source = target then by
    simp only [moveLabel, moveStore, h, ↓reduceIte]
    exact Kernel.Nop.program
  else by
    simp only [moveLabel, moveStore, h, ↓reduceIte]
    exact Kernel.RegisterGlobal.machine source target h

theorem move_supports (source target : Register) : TM2.Supports (moveProgram source target) Finset.univ := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    exact Control.Indirect.statement_support (moveProgram source target label)

/-- Actual old macro entries. None is a host program-counter cast or a
free stage switch. The outer source caller must really load initial then
jump to this local label, as Source_Family001 already implements. -/
def start (backend : RatBackend) (data : DataInstruction) : LocalLabel backend data.val := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant _ _ => exact ()
  | move target source => exact moveStart source target
  | loadInput _ _ => exact Log.InputLoad.startLabel
  | load _ _ => exact Log.HeapLoad.startLabel
  | store _ _ => exact Log.HeapStore.startLabel
  | release _ => exact Log.HeapRelease.startLabel
  | natOp _ _ _ _ => exact Kernel.NatInstruction.computeLabels 0
  | ratOp _ _ _ _ =>
      exact Kernel.CallFamily.labels Kernel.RawInstruction.LocalLabel 0 (Kernel.RawInstruction.startLabel 0)
  | natCompare _ _ _ _ => exact Codec.NatCompare.control 0
  | ratCompare _ _ _ _ =>
      exact Kernel.CallFamily.labels Kernel.RatCompare.LocalLabel 0 (Kernel.RatCompare.startLabel 0)
  | natToRat _ _ => exact Codec.NatCast.control 0
  | numeratorAbs _ _ | denominator _ _ | negative _ _ => exact Codec.FieldOps.control 0
  | output _ => exact Codec.OutputInstruction.control 0
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

/-- Only fixed finite store values occur here. Empty stack arguments
below are used to project the old macro's STORE expression; they are not
runtime workspace premises or free physical-stack initialization. -/
def initial (backend : RatBackend) (data : DataInstruction) : LocalStore backend data.val := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant _ _ => exact none
  | move target source => exact moveInitial source target
  | loadInput _ _ =>
      change Log.InputLoad.Store
      exact default
  | load _ _ =>
      change Log.HeapLoad.Store
      exact default
  | store _ _ =>
      change Log.HeapStore.Store
      exact default
  | release _ =>
      change Log.HeapRelease.Store
      exact default
  | natOp operation _ _ _ => exact (Kernel.NatInstruction.before operation (fun _ => []) none).var
  | ratOp operation _ _ _ => exact Kernel.RawInstruction.initialized (backend.states operation)
  | natCompare _ _ _ _ => exact Codec.NatCompare.clearedStore
  | ratCompare _ _ _ _ => exact Kernel.RatCompare.initialized (backend.states .subtract)
  | natToRat _ _ => exact Codec.FieldOps.clearedStore
  | numeratorAbs _ _ | denominator _ _ | negative _ _ => exact Codec.FieldOps.clearedStore
  | output _ => exact Codec.OutputInstruction.clearedStore
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

/-- The catalogue is ONLY actual old data code. The phase's fixed Bool
selects its mounted raw6/core13 bank. Constant bytes belong to a source
array fixed before all inputs. No Cell/Nat/Rat operand is put in sigma,
and no Instruction.execute/host evaluation occurs in any transition. -/
def program (backend : RatBackend) (core : Bool) (data : DataInstruction) :
    LocalLabel backend data.val → TM2.Stmt Alphabet (LocalLabel backend data.val) (LocalStore backend data.val) := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant target value => exact Kernel.RegisterGlobal.literalMachine target value
  | move target source => exact moveProgram source target
  | loadInput destination pointer => exact Log.InputLoad.program core pointer destination
  | load destination pointer => exact Log.HeapLoad.program pointer destination
  | store pointer source => exact Log.HeapStore.program pointer source
  | release pointer => exact Log.HeapRelease.program pointer
  | natOp operation target left right => exact Kernel.NatInstruction.program operation target left right
  | ratOp operation target left right => exact Kernel.RawInstruction.program (backend.machine operation) target left right
  | natCompare comparison target left right => exact Codec.NatCompare.program comparison target left right
  | ratCompare comparison target left right =>
      exact Kernel.RatCompare.program (backend.machine .subtract) comparison target left right
  | natToRat target source => exact Codec.NatCast.program target source
  | numeratorAbs target source => exact Codec.FieldOps.program .numeratorAbs target source
  | denominator target source => exact Codec.FieldOps.program .denominator target source
  | negative target source => exact Codec.FieldOps.program .negative target source
  | output source => exact Codec.OutputInstruction.program source
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

theorem supports (backend : RatBackend) (core : Bool) (data : DataInstruction) :
    TM2.Supports (program backend core data) (Finset.univ : Finset (LocalLabel backend data.val)) := by
  rcases data with ⟨instruction, eligible⟩
  cases instruction with
  | constant target value => exact Kernel.RegisterGlobal.literal_supports target value
  | move target source => exact move_supports source target
  | loadInput destination pointer => exact Log.InputLoad.supports core pointer destination
  | load destination pointer => exact Log.HeapLoad.supports pointer destination
  | store pointer source => exact Log.HeapStore.supports pointer source
  | release pointer => exact Log.HeapRelease.supports pointer
  | natOp operation target left right => exact Kernel.NatInstruction.supports operation target left right
  | ratOp operation target left right => exact Kernel.RawInstruction.supports (backend.machine operation) target left right
  | natCompare comparison target left right => exact Codec.NatCompare.supports comparison target left right
  | ratCompare comparison target left right =>
      exact Kernel.RatCompare.supports (backend.machine .subtract) comparison target left right
  | natToRat target source => exact Codec.NatCast.supports target source
  | numeratorAbs target source => exact Codec.FieldOps.supports .numeratorAbs target source
  | denominator target source => exact Codec.FieldOps.supports .denominator target source
  | negative target source => exact Codec.FieldOps.supports .negative target source
  | output source => exact Codec.OutputInstruction.supports source
  | branchZero _ _ _ | jump _ | jumpIndirect _ | halt => cases eligible

/-- The exact directory entry for one original non-control instruction.
This definition changes no physical stack and asserts no wholeReady or
post-op scratch clearing. The parent shared real clear stage is separate. -/
def before (backend : RatBackend) (data : DataInstruction) (contents : Stack → List Bool) : State backend data :=
  ⟨some (start backend data), initial backend data, contents⟩

end PDROC.BitVM.VM.ISA
