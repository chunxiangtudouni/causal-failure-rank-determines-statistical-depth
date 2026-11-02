module
public import RootB236_Controller_MaskArchive_Public003
public import Structure.RootB236_Controller_Candidate_Public_007
public import RootB236_Controller_ErasePort_Public004
public import RootB236_Controller_EraseSem_Public_002

/-! One fixed global graph. Return goto labels are statically identified
with the next real callee entry. Separate restore label regions preserve
the finite found/empty branch without a runtime tool in control. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.SelectErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
abbrev Stack := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Store (C : Type*) := C×Bool×Bool

inductive Label where
  | archive : MaskArchive.Label → Label
  | candidate : ControllerCandidate.Label → Label
  | restoreFound : MaskArchive.Label → Label
  | restoreEmpty : MaskArchive.Label → Label
  | erase : ErasePort.Label → Label
  | found | empty
  deriving DecidableEq

instance : Fintype Label where
  elems := (Finset.univ.image Label.archive) ∪ (Finset.univ.image Label.candidate) ∪
    (Finset.univ.image Label.restoreFound) ∪ (Finset.univ.image Label.restoreEmpty) ∪
    (Finset.univ.image Label.erase) ∪ {.found,.empty}
  complete := by intro point;cases point <;> simp
instance : Inhabited Label := ⟨.archive .boot⟩

abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}

def archiveLabels : MaskArchive.Label → Label
  | .done => .candidate (.inl 0)
  | point => .archive point
def candidateLabels (point : ControllerCandidate.Label) : Label :=
  if point=.inr .found then .restoreFound .boot else
    if point=.inr .empty then .restoreEmpty .boot else .candidate point
def foundRestoreLabels : MaskArchive.Label → Label
  | .done => .erase 0
  | point => .restoreFound point
def emptyRestoreLabels : MaskArchive.Label → Label
  | .done => .empty
  | point => .restoreEmpty point
def eraseLabels (point : ErasePort.Label) : Label := if point=2 then .found else .erase point

def program (found empty : Statement C) : Label → Statement C
  | .archive point => LabelMap.statement archiveLabels (MaskArchive.Public.archive4To8 .halt point)
  | .candidate point => LabelMap.statement candidateLabels (ControllerCandidate.withContext C point)
  | .restoreFound point => LabelMap.statement foundRestoreLabels (MaskArchive.Public.restore8To4 .halt point)
  | .restoreEmpty point => LabelMap.statement emptyRestoreLabels (MaskArchive.Public.restore8To4 .halt point)
  | .erase point => LabelMap.statement eraseLabels (ErasePort.program .halt point)
  | .found => found
  | .empty => empty

def source : Label → Statement C := program .halt .halt
def entry : Label := .archive .boot

theorem archive_agrees (found empty : Statement C) (point : MaskArchive.Label) (proper : point≠.done) :
    program found empty (archiveLabels point)=
      LabelMap.statement archiveLabels (MaskArchive.Public.archive4To8 .halt point) := by
  cases point <;> first | rfl | exact False.elim (proper rfl)
theorem candidate_agrees (found empty : Statement C) (point : ControllerCandidate.Label)
    (notFound : point≠.inr .found) (notEmpty : point≠.inr .empty) :
    program found empty (candidateLabels point)=
      LabelMap.statement candidateLabels (ControllerCandidate.withContext C point) := by
  simp only [candidateLabels,notFound,notEmpty,ite_false,program]
theorem found_restore_agrees (found empty : Statement C) (point : MaskArchive.Label) (proper : point≠.done) :
    program found empty (foundRestoreLabels point)=
      LabelMap.statement foundRestoreLabels (MaskArchive.Public.restore8To4 .halt point) := by
  cases point <;> first | rfl | exact False.elim (proper rfl)
theorem empty_restore_agrees (found empty : Statement C) (point : MaskArchive.Label) (proper : point≠.done) :
    program found empty (emptyRestoreLabels point)=
      LabelMap.statement emptyRestoreLabels (MaskArchive.Public.restore8To4 .halt point) := by
  cases point <;> first | rfl | exact False.elim (proper rfl)
theorem erase_agrees (found empty : Statement C) (point : ErasePort.Label) (proper : point≠2) :
    program found empty (eraseLabels point)=LabelMap.statement eraseLabels (ErasePort.program .halt point) := by
  simp only [eraseLabels,proper,ite_false,program]

def bank (background : Stack → List Bool) (candidate remaining tool cursor parked archive room temporary : List Bool) : Stack → List Bool :=
  fun point => if point=3 then candidate else if point=4 then remaining else if point=5 then tool else
    if point=6 then cursor else if point=7 then parked else if point=8 then archive else
    if point=11 then room else if point=12 then temporary else background point
def state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (candidate remaining tool cursor parked archive room temporary : List Bool) : State C :=
  ⟨some point,memory,bank background candidate remaining tool cursor parked archive room temporary⟩
def initial (background : Stack → List Bool) (memory : Store C) (eligible remaining old5 : List Bool) : State C :=
  state background entry memory eligible remaining old5 [] [] [] (ControllerCandidate.unary eligible.length) []

def Work (point : Stack) : Prop := point=3 ∨ point=4 ∨ point=5 ∨ point=6 ∨ point=7 ∨ point=8 ∨ point=11 ∨ point=12
instance (point : Stack) : Decidable (Work point) := by unfold Work;infer_instance
def support : Finset Label := Finset.univ
private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial
theorem supports (found empty : Statement C) : TM2.Supports (program found empty) support :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance
theorem found_body : source (C:=C) .found=.halt := rfl
theorem empty_body : source (C:=C) .empty=.halt := rfl

end RootB236.Controller.SelectErase
