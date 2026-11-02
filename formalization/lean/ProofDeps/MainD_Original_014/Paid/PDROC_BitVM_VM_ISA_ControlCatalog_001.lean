module

public import Paid.PDROC_BitVM_VM_ISA_Types_001
public import Paid.PDROC_BitVM_VM_Control_Contract_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.ControlCatalog

open Turing PaperProofs.Paid.Computation

/-! SOURCE-ONLY handoff, not yet compiled. Instruction is STATIC source
syntax, fixed before all P/gamma. Only ISA.ControlInstruction is exposed
as a callable catalogue; the other raw clauses are unused Unit cases. -/

def LocalLabel (code : Program) : Instruction → Type
  | .jumpIndirect _ => Control.Indirect.Label code
  | _ => Unit

def LocalStore (code : Program) : Instruction → Type
  | .branchZero _ _ _ => Kernel.Branch.Store
  | .jumpIndirect _ => Control.Indirect.Store code
  | _ => Unit

instance labelFinite (code : Program) (instruction : Instruction) : Fintype (LocalLabel code instruction) := by
  cases instruction <;> dsimp only [LocalLabel] <;> infer_instance

instance labelInhabited (code : Program) (instruction : Instruction) : Inhabited (LocalLabel code instruction) := by
  cases instruction <;> dsimp only [LocalLabel] <;> infer_instance

instance storeFinite (code : Program) (instruction : Instruction) : Fintype (LocalStore code instruction) := by
  cases instruction <;> dsimp only [LocalStore] <;> infer_instance

instance storeInhabited (code : Program) (instruction : Instruction) : Inhabited (LocalStore code instruction) := by
  cases instruction <;> dsimp only [LocalStore] <;> infer_instance

def rawStart (code : Program) (instruction : Instruction) : LocalLabel code instruction := by
  cases instruction with
  | jumpIndirect _ => exact Control.Indirect.resetEntry code
  | _ => exact ()

def rawInitial (code : Program) (instruction : Instruction) : LocalStore code instruction := default

/-- Branch is EXACT old five-pop/restore/trueHALT. Direct jump and halt
are EXACT old no-write trueHALT callees; the parent performs the real PC
transition after normal return and shared actual cleanup. Indirect is the
checked whole fixed callee, not a host logicalState evaluator. -/
def rawProgram (code : Program) (instruction : Instruction) :
    LocalLabel code instruction → TM2.Stmt Alphabet (LocalLabel code instruction) (LocalStore code instruction) := by
  cases instruction with
  | branchZero condition _ _ => exact Kernel.Branch.program (Kernel.RegisterGlobal.registerSlot condition)
  | jumpIndirect source => exact Control.Indirect.program code source
  | _ => exact Kernel.Nop.program

abbrev Label (code : Program) (instruction : ControlInstruction) := LocalLabel code instruction.val
abbrev Store (code : Program) (instruction : ControlInstruction) := LocalStore code instruction.val
abbrev State (code : Program) (instruction : ControlInstruction) :=
  TM2.Cfg Alphabet (Label code instruction) (Store code instruction)

def start (code : Program) (instruction : ControlInstruction) : Label code instruction := rawStart code instruction.val
def initial (code : Program) (instruction : ControlInstruction) : Store code instruction := rawInitial code instruction.val
def program (code : Program) (instruction : ControlInstruction) := rawProgram code instruction.val

/-- Only STATIC instruction literals and finite ACTUALLY CAPTURED flags
are read. There is no logicalState argument, runtime Nat register, unknown
Nat-to-Fin cast, source execute evaluator, answer or target parameter. -/
def rawObservedNext (code : Program) : (instruction : Instruction) → LocalStore code instruction → Option (Control.PC code)
  | .branchZero _ whenZero whenNonzero, flags =>
      if flags.1 == some false then
        if Kernel.Branch.zeroFlag flags then Control.literalPC code whenZero else Control.literalPC code whenNonzero
      else none
  | .jump target, _ => Control.literalPC code target
  | .jumpIndirect _, flags => Control.Indirect.selected code flags
  | _, _ => none

def observedNext (code : Program) (instruction : ControlInstruction) : Store code instruction → Option (Control.PC code) :=
  rawObservedNext code instruction.val

theorem raw_supports (code : Program) (instruction : Instruction) :
    TM2.Supports (rawProgram code instruction) (Finset.univ : Finset (LocalLabel code instruction)) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    exact Control.Indirect.statement_support (rawProgram code instruction label)

theorem supports (code : Program) (instruction : ControlInstruction) :
    TM2.Supports (program code instruction) (Finset.univ : Finset (Label code instruction)) :=
  raw_supports code instruction.val

/-- The old exact inspector source run, including its actual source
HALT, whole physical frame and captured finite flags. The parent family's
return adapter maps that true HALT to its real resume label. -/
theorem branch_read_runs (condition : Register) (contents : Stack → List Bool) (flags : Kernel.Branch.Store) :
    ∃ run : List Kernel.Branch.State,
      run.head? = some ⟨some (), flags, contents⟩ ∧
      run.IsChain (fun before after => TM2.step (Kernel.Branch.program (Kernel.RegisterGlobal.registerSlot condition)) before = some after) ∧
      run.getLast? = some ⟨none, Kernel.Branch.captured (contents (Kernel.RegisterGlobal.registerSlot condition)), contents⟩ ∧
      TM2.step (Kernel.Branch.program (Kernel.RegisterGlobal.registerSlot condition))
        ⟨none, Kernel.Branch.captured (contents (Kernel.RegisterGlobal.registerSlot condition)), contents⟩ = none ∧
      run.length = 2 := Kernel.Branch.runs (Kernel.RegisterGlobal.registerSlot condition) contents flags

theorem nop_runs (contents : Stack → List Bool) :
    ∃ run : List Kernel.Nop.State,
      run.head? = some ⟨some (), (), contents⟩ ∧
      run.IsChain (fun before after => TM2.step Kernel.Nop.program before = some after) ∧
      run.getLast? = some ⟨none, (), contents⟩ ∧
      TM2.step Kernel.Nop.program ⟨none, (), contents⟩ = none ∧ run.length = 2 := by
  exact ⟨[⟨some (), (), contents⟩, ⟨none, (), contents⟩], rfl,
    List.isChain_cons_cons.mpr ⟨rfl, List.isChain_singleton _⟩, rfl, rfl, rfl⟩

theorem observed_branch_natural (code : Program) (condition : Register) (whenZero whenNonzero query : Nat) :
    rawObservedNext code (.branchZero condition whenZero whenNonzero)
      (Kernel.Branch.captured (encodeCellBits (.natural query))) =
      Control.literalPC code (if query = 0 then whenZero else whenNonzero) := by
  have tag : (Kernel.Branch.captured (encodeCellBits (.natural query))).1 = some false := rfl
  change (if (Kernel.Branch.captured (encodeCellBits (.natural query))).1 == some false then
    (if Kernel.Branch.zeroFlag (Kernel.Branch.captured (encodeCellBits (.natural query))) then
      Control.literalPC code whenZero else Control.literalPC code whenNonzero) else none) = _
  rw [tag, Kernel.Branch.natural_zero]
  by_cases matched : query = 0 <;>
    simp [matched]

theorem observed_branch_rational (code : Program) (condition : Register) (whenZero whenNonzero : Nat) (query : Rat) :
    rawObservedNext code (.branchZero condition whenZero whenNonzero)
      (Kernel.Branch.captured (encodeCellBits (.rational query))) = none := by
  simp [rawObservedNext, Kernel.Branch.captured, encodeCellBits]

theorem observed_jump (code : Program) (target : Nat) :
    rawObservedNext code (.jump target) () = Control.literalPC code target := rfl

theorem observed_indirect (code : Program) (source : Register) (flags : Control.Indirect.Store code) :
    rawObservedNext code (.jumpIndirect source) flags = Control.Indirect.selected code flags := rfl

theorem observed_halt (code : Program) : rawObservedNext code .halt () = none := rfl

end PDROC.BitVM.VM.ISA.ControlCatalog
