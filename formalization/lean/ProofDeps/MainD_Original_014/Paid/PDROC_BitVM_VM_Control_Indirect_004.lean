module

public import Paid.PDROC_BitVM_VM_Control_Literal_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.BitVM.VM.Control.Indirect

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native PDROC.BitVM.Kernel.RegisterGlobal

/-- All choices are fixed SOURCE-CODE choices. In particular candidate
is Fin code.size, NEVER a runtime Nat register or word width. -/
inductive Macro (code : Program) where
  | initialClear (slot : Fin 4)
  | pointer
  | literal (candidate : PC code)
  | compare (candidate : PC code)
  | finalClear (slot : Fin 4)
  deriving DecidableEq, Fintype, Inhabited

abbrev Index (code : Program) := Macro code ⊕ Unit

def LocalLabel (code : Program) : Index code → Type
  | .inl (.initialClear _) => Log.HeapClear.Label
  | .inl .pointer => Log.HeapPointer.Label
  | .inl (.literal _) => PCLiteral.Label
  | .inl (.compare _) => Log.InputCompare.Label
  | .inl (.finalClear _) => Log.HeapClear.Label
  | .inr _ => Unit

def LocalStore (code : Program) : Index code → Type
  | .inl _ => Log.HeapPointer.Store
  | .inr _ => Option (PC code)

instance localLabelFintype (code : Program) (index : Index code) : Fintype (LocalLabel code index) := by
  cases index with
  | inl operation => cases operation <;> dsimp [LocalLabel] <;> infer_instance
  | inr marker => cases marker; dsimp [LocalLabel]; infer_instance

instance localLabelInhabited (code : Program) (index : Index code) : Inhabited (LocalLabel code index) := by
  cases index with
  | inl operation => cases operation <;> dsimp [LocalLabel] <;> infer_instance
  | inr marker => cases marker; dsimp [LocalLabel]; infer_instance

instance localStoreFintype (code : Program) (index : Index code) : Fintype (LocalStore code index) := by
  cases index <;> dsimp [LocalStore] <;> infer_instance

instance localStoreInhabited (code : Program) (index : Index code) : Inhabited (LocalStore code index) := by
  cases index <;> dsimp [LocalStore] <;> infer_instance

abbrev Label (code : Program) := Kernel.CallFamily.Label (LocalLabel code)
abbrev Store (code : Program) := Kernel.CallFamily.Store (LocalStore code)
abbrev State (code : Program) := TM2.Cfg Alphabet (Label code) (Store code)
abbrev Statement (code : Program) := TM2.Stmt Alphabet (Label code) (Store code)

def selectedIndex (code : Program) : Index code := .inr ()

def selected (code : Program) (store : Store code) : Option (PC code) := store (selectedIndex code)

def setSelected (code : Program) (value : Option (PC code)) (store : Store code) : Store code :=
  Function.update store (selectedIndex code) value

def clearSlot (slot : Fin 4) : Stack :=
  if slot = 0 then 24 else if slot = 1 then 26 else if slot = 2 then 27 else 28

def startLabel (code : Program) : (index : Index code) → LocalLabel code index
  | .inl (.initialClear _) => (0 : Log.HeapClear.Label)
  | .inl .pointer => (0 : Log.HeapPointer.Label)
  | .inl (.literal _) => PCLiteral.startLabel
  | .inl (.compare _) => Log.InputCompare.startLabel
  | .inl (.finalClear _) => (0 : Log.HeapClear.Label)
  | .inr _ => ()

def entry (code : Program) (index : Index code) : Label code :=
  Kernel.CallFamily.labels (LocalLabel code) index (startLabel code index)

def returned (code : Program) (index : Index code) : Label code :=
  Kernel.CallFamily.returnLabel (LocalLabel code) index

def cleanupEntry (code : Program) : Label code := entry code (.inl (.finalClear 0))
def resetEntry (code : Program) : Label code := entry code (selectedIndex code)

def source (code : Program) (pointer : Register) :
    (index : Index code) → LocalLabel code index → TM2.Stmt Alphabet (LocalLabel code index) (LocalStore code index)
  | .inl (.initialClear slot) => Log.HeapClear.program (clearSlot slot)
  | .inl .pointer => Log.HeapPointer.program pointer
  | .inl (.literal candidate) => PCLiteral.program (encodeNatBits candidate.val)
  | .inl (.compare _) => Log.InputCompare.program
  | .inl (.finalClear slot) => Log.HeapClear.program (clearSlot slot)
  | .inr _ => fun _ => .load (fun _ => none) .halt

/-- A compile-time successor of the finite candidate label. This never
converts the unknown source-register Nat to Fin. -/
def goCandidate (code : Program) (candidate : Option (PC code)) : Statement code :=
  .goto (fun _ => (candidate.map (fun point => entry code (.inl (.literal point)))).getD (cleanupEntry code))

def typedFlag (code : Program) (store : Store code) : Bool :=
  Log.Query.equality (store (.inl .pointer)).2.1

def equalityFlag (code : Program) (candidate : PC code) (store : Store code) : Bool :=
  Log.Query.equality (store (.inl (.compare candidate))).2.1

/-- Only REAL finite flags are tested. selected is loaded with a static
candidate ONLY in the true BoolEq branch, after actual byte comparison.
Every path then runs the SAME cleanup family before returning. -/
def resume (code : Program) : Index code → Statement code
  | .inr _ => .goto (fun _ => entry code (.inl (.initialClear 0)))
  | .inl (.initialClear slot) =>
    if bound : slot.val + 1 < 4 then
      .goto (fun _ => entry code (.inl (.initialClear ⟨slot.val + 1, bound⟩)))
    else .goto (fun _ => entry code (.inl .pointer))
  | .inl .pointer => .branch (typedFlag code)
      (goCandidate code (literalPC code 0)) (.goto (fun _ => cleanupEntry code))
  | .inl (.literal candidate) => .goto (fun _ => entry code (.inl (.compare candidate)))
  | .inl (.compare candidate) => .branch (equalityFlag code candidate)
      (.load (setSelected code (some candidate)) (.goto (fun _ => cleanupEntry code)))
      (goCandidate code (literalPC code (candidate.val + 1)))
  | .inl (.finalClear slot) =>
    if bound : slot.val + 1 < 4 then
      .goto (fun _ => entry code (.inl (.finalClear ⟨slot.val + 1, bound⟩)))
    else .halt

def program (code : Program) (pointer : Register) :=
  Kernel.CallFamily.machine (LocalLabel code) (LocalStore code) (source code pointer) (resume code)

/-- Any fixed finite control statement has its goto targets in the full
finite support. This introduces no data-dependent alphabet or store. -/
theorem statement_support {Λ σ : Type*} [Fintype Λ] (statement : TM2.Stmt Alphabet Λ σ) :
    TM2.SupportsStmt (Finset.univ : Finset Λ) statement := by
  induction statement <;> simp_all [TM2.SupportsStmt]

theorem source_supports (code : Program) (pointer : Register) (index : Index code) :
    TM2.Supports (source code pointer index) (Finset.univ : Finset (LocalLabel code index)) := by
  cases index with
  | inr marker =>
    cases marker
    exact ⟨by simp, fun label _ => statement_support (source code pointer (.inr ()) label)⟩
  | inl operation =>
    cases operation with
    | initialClear slot => exact Log.HeapClear.supports (clearSlot slot)
    | pointer => exact Log.HeapPointer.supports pointer
    | literal candidate => exact PCLiteral.supports (encodeNatBits candidate.val)
    | compare candidate => exact Log.InputCompare.supports
    | finalClear slot => exact Log.HeapClear.supports (clearSlot slot)

theorem supports (code : Program) (pointer : Register) :
    TM2.Supports (program code pointer) (Finset.univ : Finset (Label code)) :=
  Kernel.CallFamily.supports (LocalLabel code) (LocalStore code) (source code pointer) (resume code)
    (source_supports code pointer) (fun index => statement_support (resume code index))

theorem selected_set (code : Program) (value : Option (PC code)) (store : Store code) :
    selected code (setSelected code value store) = value := by
  change Function.update store (selectedIndex code) value (selectedIndex code) = value
  exact Function.update_self _ _ _

theorem compare_true_edge (code : Program) (pointer : Register) (candidate : PC code)
    (store : Store code) (contents : Stack → List Bool) (equal : equalityFlag code candidate store = true) :
    TM2.step (program code pointer) (⟨some (returned code (.inl (.compare candidate))), store, contents⟩ : State code) =
      some ⟨some (cleanupEntry code), setSelected code (some candidate) store, contents⟩ := by
  change some (TM2.stepAux (resume code (.inl (.compare candidate))) store contents) = _
  simp only [resume, TM2.stepAux, equal]
  rfl

theorem compare_false_edge (code : Program) (pointer : Register) (candidate : PC code)
    (store : Store code) (contents : Stack → List Bool) (different : equalityFlag code candidate store = false) :
    TM2.step (program code pointer) (⟨some (returned code (.inl (.compare candidate))), store, contents⟩ : State code) =
      some ⟨some (((literalPC code (candidate.val + 1)).map
        (fun point => entry code (.inl (.literal point)))).getD (cleanupEntry code)), store, contents⟩ := by
  change some (TM2.stepAux (resume code (.inl (.compare candidate))) store contents) = _
  simp only [resume, TM2.stepAux, different, goCandidate]
  rfl

end PDROC.BitVM.VM.Control.Indirect
