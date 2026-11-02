module

public import Paid.PDROC_BitVM_Kernel_RatFamily_054
public import Paid.PDROC_BitVM_Kernel_RatCompare_051
public import Paid.PDROC_BitVM_Kernel_Nop_050
public import Paid.PDROC_BitVM_Kernel_NatInstruction_014
public import Paid.PDROC_BitVM_Log_InputLoad_059
public import Paid.PDROC_BitVM_Log_HeapLoad_033
public import Paid.PDROC_BitVM_Log_HeapStore_026
public import Paid.PDROC_BitVM_Log_HeapRelease_020
public import Paid.PDROC_BitVM_Codec_NatCompare_032
public import Paid.PDROC_BitVM_Codec_NatCast_027
public import Paid.PDROC_BitVM_Codec_FieldOps_022
public import Paid.PDROC_BitVM_Codec_OutputInstruction_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.ISA

open Turing PaperProofs.Paid.Computation

abbrev Stack := Kernel.RegisterGlobal.Stack
abbrev Alphabet := Kernel.RegisterGlobal.Alphabet

/-- Static compilation metadata, selected ONCE before every original
input. The four machines come from the actual uniform native family.
No rational/natural operand is a field of a runtime macro store. -/
structure RatBackend where
  states : RatOp → ℕ
  c : RatOp → ℕ
  d : RatOp → ℕ
  machine : ∀ operation, PaperProofs.Common.Native.RationalControllerComputation.Machine (states operation)
  valid : ∀ operation, 0 < c operation ∧ 0 < d operation ∧
    Kernel.RawOp.NativeContract (machine operation) (Kernel.RawInstruction.resultFunction operation)
      (c operation) (d operation) ∧
    Kernel.RawInstruction.Matches operation (Kernel.RawInstruction.resultFunction operation)

theorem ratBackend_exists : Nonempty RatBackend := by
  obtain ⟨states, c, d, machine, valid⟩ := Kernel.RawInstruction.uniform_family
  exact ⟨⟨states, c, d, machine, valid⟩⟩

noncomputable def fixedRatBackend : RatBackend := Classical.choice ratBackend_exists

/-- Infinite original Instruction is STATIC source syntax, not a runtime
label/index type. The compiler consumes a source array fixed before all
P/gamma using its finite positions. Control cases remain separate ports. -/
def isControl : Instruction → Bool
  | .branchZero _ _ _ | .jump _ | .jumpIndirect _ | .halt => true
  | _ => false

abbrev DataInstruction := {instruction : Instruction // isControl instruction = false}
abbrev ControlInstruction := {instruction : Instruction // isControl instruction = true}

def classify (instruction : Instruction) : DataInstruction ⊕ ControlInstruction :=
  if h : isControl instruction then .inr ⟨instruction, h⟩
  else .inl ⟨instruction, Bool.eq_false_iff.mpr h⟩

/-- Same-register move has its genuine one-step Nop callee; the distinct
case is exactly the original clear/copy/restore register machine. -/
def moveLabel (source target : Register) : Type := if source = target then Unit else Kernel.RegisterMove.Label
def moveStore (source target : Register) : Type := if source = target then Unit else Kernel.RegisterMove.Store

instance moveLabelFinite (source target : Register) : Fintype (moveLabel source target) := by
  unfold moveLabel
  split_ifs <;> infer_instance

instance moveLabelInhabited (source target : Register) : Inhabited (moveLabel source target) := by
  unfold moveLabel
  split_ifs <;> infer_instance

instance moveStoreFinite (source target : Register) : Fintype (moveStore source target) := by
  unfold moveStore
  split_ifs <;> infer_instance

/-- These types contain only the old fixed finite labels. A source-code
literal is deliberately ignored by the label/store types: its bits are
part of fixed code, never Cell/Nat/Rat in runtime sigma. Unit for control
cases is unused: program below is defined ONLY on DataInstruction. -/
def LocalLabel (_backend : RatBackend) : Instruction → Type
  | .constant _ _ => Unit
  | .move target source => moveLabel source target
  | .loadInput _ _ => Log.InputLoad.Label
  | .load _ _ => Log.HeapLoad.Label
  | .store _ _ => Log.HeapStore.Label
  | .release _ => Log.HeapRelease.Label
  | .natOp _ _ _ _ => Kernel.NatInstruction.FullLabel
  | .ratOp _ _ _ _ => Kernel.RawInstruction.Label
  | .natCompare _ _ _ _ => Codec.NatCompare.Label
  | .ratCompare _ _ _ _ => Kernel.RatCompare.Label
  | .natToRat _ _ => Codec.NatCast.Label
  | .numeratorAbs _ _ | .denominator _ _ | .negative _ _ => Codec.FieldOps.Label
  | .output _ => Codec.OutputInstruction.Label
  | .branchZero _ _ _ | .jump _ | .jumpIndirect _ | .halt => Unit

def LocalStore (backend : RatBackend) : Instruction → Type
  | .constant _ _ => Option Bool
  | .move target source => moveStore source target
  | .loadInput _ _ => Log.InputLoad.Store
  | .load _ _ => Log.HeapLoad.Store
  | .store _ _ => Log.HeapStore.Store
  | .release _ => Log.HeapRelease.Store
  | .natOp operation _ _ _ => Kernel.NatInstruction.FullStore operation
  | .ratOp operation _ _ _ => Kernel.RawInstruction.Store (backend.states operation)
  | .natCompare _ _ _ _ => Codec.NatCompare.Store
  | .ratCompare _ _ _ _ => Kernel.RatCompare.Store (backend.states .subtract)
  | .natToRat _ _ => Codec.NatCast.Store
  | .numeratorAbs _ _ | .denominator _ _ | .negative _ _ => Codec.FieldOps.Store
  | .output _ => Codec.OutputInstruction.Store
  | .branchZero _ _ _ | .jump _ | .jumpIndirect _ | .halt => Unit

instance labelFinite (backend : RatBackend) (instruction : Instruction) : Fintype (LocalLabel backend instruction) := by
  cases instruction <;> dsimp only [LocalLabel] <;> infer_instance

instance labelInhabited (backend : RatBackend) (instruction : Instruction) : Inhabited (LocalLabel backend instruction) := by
  cases instruction <;> dsimp only [LocalLabel] <;> infer_instance

instance storeFinite (backend : RatBackend) (instruction : Instruction) : Fintype (LocalStore backend instruction) := by
  cases instruction <;> dsimp only [LocalStore] <;> infer_instance

abbrev State (backend : RatBackend) (instruction : DataInstruction) :=
  TM2.Cfg Alphabet (LocalLabel backend instruction.val) (LocalStore backend instruction.val)

end PDROC.BitVM.VM.ISA
