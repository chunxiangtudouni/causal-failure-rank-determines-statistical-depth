module

public import Paid.PDROC_BitVM_VM_CFG_Program_001
public import Paid.PDROC_BitVM_VM_Source_Dispatch_005
public import Paid.PDROC_BitVM_VM_Cleanup_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Program

open Turing PaperProofs.Paid.Computation

/-! A single shared genuine cleaner and a separate finite metadata
component. Cleaner entry resets only cleaner flags. The next-PC field
survives that real reset, and every original opcode, including fetched
halt, returns through this physical cleanup. Final serialization is a
later phase and MUST NOT be routed back through the zero-clearing stage. -/

abbrev Phase (code : Program) := Source.Dispatch.Phase (PC code)
abbrev Label (backend : ISA.RatBackend) (code : Program) :=
  Source.Dispatch.Label (OpcodeLabel backend code) Cleanup.Label
abbrev Store (backend : ISA.RatBackend) (code : Program) :=
  Source.Dispatch.Store (OpcodeStore backend code) (Cleanup.Store Unit)
abbrev State (backend : ISA.RatBackend) (code : Program) :=
  TM2.Cfg ISA.Alphabet (Label backend code) (Store backend code)

instance labelFinite (backend : ISA.RatBackend) (code : Program) : Fintype (Label backend code) :=
  inferInstance

instance labelInhabited (backend : ISA.RatBackend) (code : Program) : Inhabited (Label backend code) :=
  inferInstance

instance storeFinite (backend : ISA.RatBackend) (code : Program) : Fintype (Store backend code) :=
  inferInstance

def localStart (backend : ISA.RatBackend) (code : Program) :=
  Source.Dispatch.start (OpcodeLabel backend code) Cleanup.Label (opcodeStart backend code) Cleanup.startLabel

def localInitial (backend : ISA.RatBackend) (code : Program) :=
  Source.Dispatch.initial (OpcodeStore backend code) (Cleanup.Store Unit) (opcodeInitial backend code) (none, ())

/-- A fixed finite initial store. No physical contents are initialized
by this definition: the caller's entry statement really loads the active
local store, and the physical cleaner is executable old code. -/
def initial (backend : ISA.RatBackend) (code : Program) : Store backend code := localInitial backend code

instance storeInhabited (backend : ISA.RatBackend) (code : Program) : Inhabited (Store backend code) :=
  ⟨initial backend code⟩

def selected (backend : ISA.RatBackend) (code : Program) (store : Store backend code) : Option (PC code) :=
  Source.Dispatch.selected (OpcodeStore backend code) (Cleanup.Store Unit) store

def setSelected (backend : ISA.RatBackend) (code : Program) (next : Option (PC code))
    (store : Store backend code) : Store backend code :=
  Source.Dispatch.setSelected (OpcodeStore backend code) (Cleanup.Store Unit) next store

def chooseNext (backend : ISA.RatBackend) (code : Program) (pc : PC code)
    (store : Store backend code) : Option (PC code) :=
  opcodeNext backend code pc (store (.opcode pc))

def program (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    Label backend code → TM2.Stmt ISA.Alphabet (Label backend code) (Store backend code) :=
  Source.Dispatch.program (OpcodeLabel backend code) (OpcodeStore backend code) Cleanup.Label (Cleanup.Store Unit)
    (opcodeProgram backend core code) (opcodeStart backend code) (opcodeInitial backend code)
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) (chooseNext backend code)

theorem supports (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    TM2.Supports (program backend core code) (Finset.univ : Finset (Label backend code)) := by
  exact Source.Dispatch.supports (OpcodeLabel backend code) (OpcodeStore backend code) Cleanup.Label (Cleanup.Store Unit)
    (opcodeProgram backend core code) (opcodeStart backend code) (opcodeInitial backend code)
    (Cleanup.program Unit) Cleanup.startLabel (none, ()) (chooseNext backend code)
    (opcode_supports backend core code) (Cleanup.supports Unit)

def phaseEntry (backend : ISA.RatBackend) (code : Program) (phase : Phase code) : Label backend code :=
  Source.entryLabel (Source.Dispatch.LocalLabel (OpcodeLabel backend code) Cleanup.Label) phase

def phaseReturn (backend : ISA.RatBackend) (code : Program) (phase : Phase code) : Label backend code :=
  Source.returnLabel (Source.Dispatch.LocalLabel (OpcodeLabel backend code) Cleanup.Label) phase

def entry (backend : ISA.RatBackend) (code : Program) (pc : PC code) : Label backend code :=
  phaseEntry backend code (.opcode pc)

def cleanupEntry (backend : ISA.RatBackend) (code : Program) : Label backend code :=
  phaseEntry backend code .cleanup

def metadataHalt (backend : ISA.RatBackend) (code : Program) : Label backend code :=
  phaseReturn backend code .metadata

def atEntry (backend : ISA.RatBackend) (code : Program) (pc : PC code)
    (store : Store backend code) (contents : ISA.Stack → List Bool) : State backend code :=
  ⟨some (entry backend code pc), store, contents⟩

/-- Empty code has no invented Fin witness: its static start is the
real metadata HALT port. Nonempty code starts at its actual entry/reset
port for position zero. No P/gamma or logical input participates here. -/
def start (backend : ISA.RatBackend) (code : Program) : Label backend code :=
  ((Control.literalPC code 0).map (entry backend code)).getD (metadataHalt backend code)

def before (backend : ISA.RatBackend) (code : Program) (contents : ISA.Stack → List Bool) : State backend code :=
  ⟨some (start backend code), initial backend code, contents⟩

end PDROC.BitVM.VM.CFG.Program
