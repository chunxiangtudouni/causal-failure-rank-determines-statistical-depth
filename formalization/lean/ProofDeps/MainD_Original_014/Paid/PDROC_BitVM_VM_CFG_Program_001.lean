module

public import Paid.PDROC_BitVM_VM_ISA_Macros_002
public import Paid.PDROC_BitVM_VM_ISA_ControlCatalog_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Program

open Turing PaperProofs.Paid.Computation

/-! SOURCE-ONLY assembly. The original array and backend are STATIC
compilation parameters, fixed before every P/gamma and physical input.
Only its bounded positions are runtime indices. Instruction, Cell, Nat
and Rat operands are not fields of any new runtime label or store. -/

abbrev PC (code : Program) := Control.PC code
abbrev Choice := ISA.DataInstruction ⊕ ISA.ControlInstruction

def localChoice (code : Program) (pc : PC code) : Choice :=
  ISA.classify (code[pc.val]'pc.isLt)

def ChoiceLabel (backend : ISA.RatBackend) (code : Program) : Choice → Type
  | .inl data => ISA.LocalLabel backend data.val
  | .inr instruction => ISA.ControlCatalog.Label code instruction

def ChoiceStore (backend : ISA.RatBackend) (code : Program) : Choice → Type
  | .inl data => ISA.LocalStore backend data.val
  | .inr instruction => ISA.ControlCatalog.Store code instruction

instance choiceLabelFinite (backend : ISA.RatBackend) (code : Program) (choice : Choice) :
    Fintype (ChoiceLabel backend code choice) := by
  cases choice <;> dsimp only [ChoiceLabel] <;> infer_instance

instance choiceLabelInhabited (backend : ISA.RatBackend) (code : Program) (choice : Choice) :
    Inhabited (ChoiceLabel backend code choice) := by
  cases choice <;> dsimp only [ChoiceLabel] <;> infer_instance

instance choiceStoreFinite (backend : ISA.RatBackend) (code : Program) (choice : Choice) :
    Fintype (ChoiceStore backend code choice) := by
  cases choice <;> dsimp only [ChoiceStore] <;> infer_instance

def choiceStart (backend : ISA.RatBackend) (code : Program) :
    (choice : Choice) → ChoiceLabel backend code choice
  | .inl data => ISA.start backend data
  | .inr instruction => ISA.ControlCatalog.start code instruction

def choiceInitial (backend : ISA.RatBackend) (code : Program) :
    (choice : Choice) → ChoiceStore backend code choice
  | .inl data => ISA.initial backend data
  | .inr instruction => ISA.ControlCatalog.initial code instruction

def choiceProgram (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    (choice : Choice) → ChoiceLabel backend code choice →
      TM2.Stmt ISA.Alphabet (ChoiceLabel backend code choice) (ChoiceStore backend code choice)
  | .inl data => ISA.program backend core data
  | .inr instruction => ISA.ControlCatalog.program code instruction

theorem choice_supports (backend : ISA.RatBackend) (core : Bool) (code : Program) (choice : Choice) :
    TM2.Supports (choiceProgram backend core code choice)
      (Finset.univ : Finset (ChoiceLabel backend code choice)) := by
  cases choice with
  | inl data => exact ISA.supports backend core data
  | inr instruction => exact ISA.ControlCatalog.supports code instruction

abbrev OpcodeLabel (backend : ISA.RatBackend) (code : Program) (pc : PC code) :=
  ChoiceLabel backend code (localChoice code pc)
abbrev OpcodeStore (backend : ISA.RatBackend) (code : Program) (pc : PC code) :=
  ChoiceStore backend code (localChoice code pc)

def opcodeStart (backend : ISA.RatBackend) (code : Program) (pc : PC code) : OpcodeLabel backend code pc :=
  choiceStart backend code (localChoice code pc)

def opcodeInitial (backend : ISA.RatBackend) (code : Program) (pc : PC code) : OpcodeStore backend code pc :=
  choiceInitial backend code (localChoice code pc)

def opcodeProgram (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : PC code) :
    OpcodeLabel backend code pc → TM2.Stmt ISA.Alphabet (OpcodeLabel backend code pc) (OpcodeStore backend code pc) :=
  choiceProgram backend core code (localChoice code pc)

theorem opcode_supports (backend : ISA.RatBackend) (core : Bool) (code : Program) (pc : PC code) :
    TM2.Supports (opcodeProgram backend core code pc) (Finset.univ : Finset (OpcodeLabel backend code pc)) :=
  choice_supports backend core code (localChoice code pc)

/-- Data continuation is a STATIC next-position literal. The control
case only reads its old actually captured finite flags. In particular,
indirect selection is the actual scanner's Option(Fin code.size).
This is not Instruction.execute or a query of host logical RAM state. -/
def choiceNext (backend : ISA.RatBackend) (code : Program) (pc : PC code) :
    (choice : Choice) → ChoiceStore backend code choice → Option (PC code)
  | .inl _, _ => Control.literalPC code (pc.val + 1)
  | .inr instruction, flags => ISA.ControlCatalog.observedNext code instruction flags

def opcodeNext (backend : ISA.RatBackend) (code : Program) (pc : PC code)
    (flags : OpcodeStore backend code pc) : Option (PC code) :=
  choiceNext backend code pc (localChoice code pc) flags

theorem choiceNext_data (backend : ISA.RatBackend) (code : Program) (pc : PC code)
    (data : ISA.DataInstruction) (flags : ISA.LocalStore backend data.val) :
    choiceNext backend code pc (.inl data) flags = Control.literalPC code (pc.val + 1) := rfl

theorem choiceNext_control (backend : ISA.RatBackend) (code : Program) (pc : PC code)
    (instruction : ISA.ControlInstruction) (flags : ISA.ControlCatalog.Store code instruction) :
    choiceNext backend code pc (.inr instruction) flags = ISA.ControlCatalog.observedNext code instruction flags := rfl

end PDROC.BitVM.VM.CFG.Program
