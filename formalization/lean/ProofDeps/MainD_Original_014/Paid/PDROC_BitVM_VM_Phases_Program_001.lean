module

public import Paid.PDROC_BitVM_VM_CFG_Program_003
public import Paid.PDROC_BitVM_Codec_Finalize_002
public import Paid.PDROC_BitVM_Log_BankMount_055
public import Paid.PDROC_BitVM_Kernel_Reset_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Phases

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-- All eight phases share the SAME physical32 Bool stacks. In
particular the prepare output is encoded by real Finalize code and
physically remounted before the core reset. No bank or tape is swapped
by this caller, and the final artifact is not sent through cleanup0. -/
inductive Phase where
  | mountRaw | resetPrepare | prepare | finalizePrepare
  | mountPrepared | resetCore | core | finalizeCore
  deriving DecidableEq, Inhabited

instance : Fintype Phase :=
  ⟨{.mountRaw, .resetPrepare, .prepare, .finalizePrepare,
      .mountPrepared, .resetCore, .core, .finalizeCore},
    by intro phase; cases phase <;> simp⟩

def LocalLabel (backend : ISA.RatBackend) (prepareCode coreCode : Program) : Phase → Type
  | .mountRaw | .mountPrepared => Log.BankMount.Label
  | .resetPrepare | .resetCore => Kernel.Reset.Label
  | .prepare => CFG.Program.Label backend prepareCode
  | .core => CFG.Program.Label backend coreCode
  | .finalizePrepare | .finalizeCore => Codec.Finalize.Label

def LocalStore (backend : ISA.RatBackend) (prepareCode coreCode : Program) : Phase → Type
  | .mountRaw | .mountPrepared => Log.BankMount.Store
  | .resetPrepare | .resetCore => Kernel.Reset.Store
  | .prepare => CFG.Program.Store backend prepareCode
  | .core => CFG.Program.Store backend coreCode
  | .finalizePrepare | .finalizeCore => Codec.Finalize.SourceStore

instance localLabelFinite (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :
    Fintype (LocalLabel backend prepareCode coreCode phase) := by
  cases phase <;> dsimp [LocalLabel] <;> infer_instance

instance localLabelInhabited (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :
    Inhabited (LocalLabel backend prepareCode coreCode phase) := by
  cases phase <;> dsimp [LocalLabel] <;> infer_instance

instance localStoreFinite (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :
    Fintype (LocalStore backend prepareCode coreCode phase) := by
  cases phase <;> dsimp [LocalStore] <;> infer_instance

def start (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    ∀ phase, LocalLabel backend prepareCode coreCode phase
  | .mountRaw | .mountPrepared => Log.BankMount.startLabel
  | .resetPrepare | .resetCore => Kernel.Reset.clearLabel 0
  | .prepare => CFG.Program.start backend prepareCode
  | .core => CFG.Program.start backend coreCode
  | .finalizePrepare | .finalizeCore => (16 : Codec.Finalize.Label)

def initial (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    ∀ phase, LocalStore backend prepareCode coreCode phase
  | .mountRaw | .mountPrepared => (default : Log.BankMount.Store)
  | .resetPrepare | .resetCore => (none,())
  | .prepare => CFG.Program.initial backend prepareCode
  | .core => CFG.Program.initial backend coreCode
  | .finalizePrepare | .finalizeCore => (default : Codec.Finalize.SourceStore)

def source (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    ∀ phase, LocalLabel backend prepareCode coreCode phase →
      TM2.Stmt ISA.Alphabet (LocalLabel backend prepareCode coreCode phase) (LocalStore backend prepareCode coreCode phase)
  | .mountRaw => Log.BankMount.program false
  | .mountPrepared => Log.BankMount.program true
  | .resetPrepare | .resetCore => Kernel.Reset.program
  | .prepare => CFG.Program.program backend false prepareCode
  | .core => CFG.Program.program backend true coreCode
  | .finalizePrepare | .finalizeCore => Codec.Finalize.program

abbrev Label (backend : ISA.RatBackend) (prepareCode coreCode : Program) :=
  Kernel.CallFamily.Label (LocalLabel backend prepareCode coreCode)
abbrev Store (backend : ISA.RatBackend) (prepareCode coreCode : Program) :=
  Kernel.CallFamily.Store (LocalStore backend prepareCode coreCode)
abbrev State (backend : ISA.RatBackend) (prepareCode coreCode : Program) :=
  TM2.Cfg ISA.Alphabet (Label backend prepareCode coreCode) (Store backend prepareCode coreCode)

instance labelInhabited (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    Inhabited (Label backend prepareCode coreCode) :=
  ⟨Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) .mountRaw
    (start backend prepareCode coreCode .mountRaw)⟩

instance storeInhabited (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    Inhabited (Store backend prepareCode coreCode) := ⟨initial backend prepareCode coreCode⟩

def entry (backend : ISA.RatBackend) (prepareCode coreCode : Program) (phase : Phase) :
    TM2.Stmt ISA.Alphabet (Label backend prepareCode coreCode) (Store backend prepareCode coreCode) :=
  .load (fun store => Function.update store phase (initial backend prepareCode coreCode phase))
    (.goto (fun _ => Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) phase
      (start backend prepareCode coreCode phase)))

def resume (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    Phase → TM2.Stmt ISA.Alphabet (Label backend prepareCode coreCode) (Store backend prepareCode coreCode)
  | .mountRaw => entry backend prepareCode coreCode .resetPrepare
  | .resetPrepare => entry backend prepareCode coreCode .prepare
  | .prepare => entry backend prepareCode coreCode .finalizePrepare
  | .finalizePrepare => entry backend prepareCode coreCode .mountPrepared
  | .mountPrepared => entry backend prepareCode coreCode .resetCore
  | .resetCore => entry backend prepareCode coreCode .core
  | .core => entry backend prepareCode coreCode .finalizeCore
  | .finalizeCore => .halt

def program (backend : ISA.RatBackend) (prepareCode coreCode : Program) :
    Label backend prepareCode coreCode → TM2.Stmt ISA.Alphabet (Label backend prepareCode coreCode) (Store backend prepareCode coreCode) :=
  Kernel.CallFamily.machine (LocalLabel backend prepareCode coreCode) (LocalStore backend prepareCode coreCode)
    (source backend prepareCode coreCode) (resume backend prepareCode coreCode)

def before (backend : ISA.RatBackend) (prepareCode coreCode : Program) (contents : ISA.Stack → List Bool) :
    State backend prepareCode coreCode :=
  ⟨some (Kernel.CallFamily.labels (LocalLabel backend prepareCode coreCode) .mountRaw
    (start backend prepareCode coreCode .mountRaw)),initial backend prepareCode coreCode,contents⟩

end PDROC.BitVM.VM.Phases
