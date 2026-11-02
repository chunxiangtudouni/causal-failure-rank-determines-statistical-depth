module

public import Paid.PDROC_BitVM_VM_Source_Family_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.VM.Source.Dispatch

open Turing PDROC.BitVM.Native

variable {K I : Type} [DecidableEq K] [DecidableEq I]

/-- Metadata is a finite caller field, never an original source opcode.
The single physical cleaner is shared by every static program counter. -/
inductive Phase (I : Type) where
  | opcode (index : I)
  | cleanup
  | metadata
  deriving DecidableEq, Fintype

instance phaseInhabited : Inhabited (Phase I) := ⟨.cleanup⟩

variable (Λ σ : I → Type) (C τ : Type)

def LocalLabel : Phase I → Type _
  | .opcode index => Λ index
  | .cleanup => C
  | .metadata => Unit

def LocalStore : Phase I → Type _
  | .opcode index => σ index
  | .cleanup => τ
  | .metadata => Option I

instance localLabelFintype [∀ index, Fintype (Λ index)] [Fintype C] (phase : Phase I) :
    Fintype (LocalLabel Λ C phase) := by
  cases phase <;> dsimp [LocalLabel] <;> infer_instance

instance localLabelInhabited [∀ index, Inhabited (Λ index)] [Inhabited C] (phase : Phase I) :
    Inhabited (LocalLabel Λ C phase) := by
  cases phase <;> dsimp [LocalLabel] <;> infer_instance

instance localStoreFintype [Fintype I] [∀ index, Fintype (σ index)] [Fintype τ] (phase : Phase I) :
    Fintype (LocalStore σ τ phase) := by
  cases phase <;> dsimp [LocalStore] <;> infer_instance

abbrev Label := Source.Label (LocalLabel Λ C)
abbrev Store := Source.Store (LocalStore σ τ)

instance labelInhabited : Inhabited (Label Λ C) :=
  ⟨Source.entryLabel (LocalLabel Λ C) .cleanup⟩

def selected (store : Store σ τ) : Option I := store .metadata

def setSelected (next : Option I) (store : Store σ τ) : Store σ τ :=
  Function.update store .metadata next

def start (opcodeStart : ∀ index, Λ index) (cleanupStart : C) : ∀ phase, LocalLabel Λ C phase
  | .opcode index => opcodeStart index
  | .cleanup => cleanupStart
  | .metadata => ()

def initial (opcodeInitial : ∀ index, σ index) (cleanupInitial : τ) : ∀ phase, LocalStore σ τ phase
  | .opcode index => opcodeInitial index
  | .cleanup => cleanupInitial
  | .metadata => none

def source
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) :
    ∀ phase, LocalLabel Λ C phase → TM2.Stmt (fun _ : K => Bool) (LocalLabel Λ C phase) (LocalStore σ τ phase)
  | .opcode index => opcode index
  | .cleanup => cleanup
  | .metadata => fun _ => .halt

/-- A choice here reads only fixed finite caller flags. Its actual
opcode instances use static literals, captured branch bits, or the
indirect scanner's actual Option(Fin code.size), never host RAM values. -/
def resume (chooseNext : I → Store σ τ → Option I) :
    Phase I → TM2.Stmt (fun _ : K => Bool) (Label Λ C) (Store σ τ)
  | .opcode index => .load (fun store => setSelected σ τ (chooseNext index store) store)
      (.goto (fun _ => Source.entryLabel (LocalLabel Λ C) .cleanup))
  | .cleanup => .goto (fun store =>
      ((selected σ τ store).map (fun index => Source.entryLabel (LocalLabel Λ C) (.opcode index))).getD
        (Source.returnLabel (LocalLabel Λ C) .metadata))
  | .metadata => .halt

def program
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I) :
    Label Λ C → TM2.Stmt (fun _ : K => Bool) (Label Λ C) (Store σ τ) :=
  Source.program (LocalLabel Λ C) (LocalStore σ τ) (source Λ σ C τ opcode cleanup)
    (start Λ C opcodeStart cleanupStart) (initial σ τ opcodeInitial cleanupInitial)
    (resume Λ σ C τ chooseNext)

theorem selected_set (next : Option I) (store : Store σ τ) :
    selected σ τ (setSelected σ τ next store) = next := by
  change Function.update store (Phase.metadata : Phase I) next Phase.metadata = next
  exact Function.update_self Phase.metadata next store

/-- The cleaner's real entry reset changes only its own local finite
store. The selected PC survives in the distinct metadata component. -/
theorem cleanup_reset_preserves_selected (opcodeInitial : ∀ index, σ index) (cleanupInitial : τ)
    (store : Store σ τ) :
    selected σ τ (Function.update store .cleanup (initial σ τ opcodeInitial cleanupInitial .cleanup)) =
      selected σ τ store := by
  exact Function.update_of_ne (by intro same; cases same) _ _

theorem opcode_return_edge
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I) (index : I) (store : Store σ τ) (contents : K → List Bool) :
    TM2.step (program Λ σ C τ opcode opcodeStart opcodeInitial cleanup cleanupStart cleanupInitial chooseNext)
      (⟨some (Source.returnLabel (LocalLabel Λ C) (.opcode index)),store,contents⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label Λ C) (Store σ τ)) =
      some (Source.entryState (LocalLabel Λ C) (LocalStore σ τ) .cleanup
        (setSelected σ τ (chooseNext index store) store) contents) := rfl

theorem cleanup_return_some
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I) (index : I) (store : Store σ τ) (contents : K → List Bool)
    (observed : selected σ τ store = some index) :
    TM2.step (program Λ σ C τ opcode opcodeStart opcodeInitial cleanup cleanupStart cleanupInitial chooseNext)
      (⟨some (Source.returnLabel (LocalLabel Λ C) .cleanup),store,contents⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label Λ C) (Store σ τ)) =
      some (Source.entryState (LocalLabel Λ C) (LocalStore σ τ) (.opcode index) store contents) := by
  change some (TM2.stepAux (.goto (fun finiteStore =>
    ((selected σ τ finiteStore).map (fun next => Source.entryLabel (LocalLabel Λ C) (.opcode next))).getD
      (Source.returnLabel (LocalLabel Λ C) .metadata))) store contents) = _
  simp only [TM2.stepAux,observed,Option.map_some,Option.getD_some]
  rfl

theorem cleanup_return_none
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I) (store : Store σ τ) (contents : K → List Bool)
    (observed : selected σ τ store = none) :
    TM2.step (program Λ σ C τ opcode opcodeStart opcodeInitial cleanup cleanupStart cleanupInitial chooseNext)
      (⟨some (Source.returnLabel (LocalLabel Λ C) .cleanup),store,contents⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label Λ C) (Store σ τ)) =
      some ⟨some (Source.returnLabel (LocalLabel Λ C) .metadata),store,contents⟩ := by
  change some (TM2.stepAux (.goto (fun finiteStore =>
    ((selected σ τ finiteStore).map (fun next => Source.entryLabel (LocalLabel Λ C) (.opcode next))).getD
      (Source.returnLabel (LocalLabel Λ C) .metadata))) store contents) = _
  simp only [TM2.stepAux,observed,Option.map_none,Option.getD_none]

theorem metadata_halt_edge
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I) (store : Store σ τ) (contents : K → List Bool) :
    TM2.step (program Λ σ C τ opcode opcodeStart opcodeInitial cleanup cleanupStart cleanupInitial chooseNext)
      (⟨some (Source.returnLabel (LocalLabel Λ C) .metadata),store,contents⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label Λ C) (Store σ τ)) = some ⟨none,store,contents⟩ := rfl

variable [Fintype I] [∀ index, Fintype (Λ index)] [∀ index, Inhabited (Λ index)]
variable [Fintype C] [Inhabited C]

omit [DecidableEq K] in
theorem supports
    (opcode : ∀ index, Λ index → TM2.Stmt (fun _ : K => Bool) (Λ index) (σ index))
    (opcodeStart : ∀ index, Λ index) (opcodeInitial : ∀ index, σ index)
    (cleanup : C → TM2.Stmt (fun _ : K => Bool) C τ) (cleanupStart : C) (cleanupInitial : τ)
    (chooseNext : I → Store σ τ → Option I)
    (opcodeClosed : ∀ index, TM2.Supports (opcode index) (Finset.univ : Finset (Λ index)))
    (cleanupClosed : TM2.Supports cleanup (Finset.univ : Finset C)) :
    TM2.Supports (program Λ σ C τ opcode opcodeStart opcodeInitial cleanup cleanupStart cleanupInitial chooseNext)
      (Finset.univ : Finset (Label Λ C)) := by
  apply Source.supports
  · intro phase
    cases phase with
    | opcode index => exact opcodeClosed index
    | cleanup => exact cleanupClosed
    | metadata =>
      constructor
      · exact Finset.mem_univ _
      · intro marker _
        cases marker
        trivial
  · intro phase
    cases phase <;> simp [resume,TM2.SupportsStmt]

end PDROC.BitVM.VM.Source.Dispatch
