module
public import RootB236_Controller_SelectErase_Public006

/-! Only a new real clear4 entry is added. The complete frozen27-label
select/restore/erase source is transported as code, and continuation
enters its scanner clear5 label directly, with the physical cursor kept. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.ResumeErase
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
abbrev Stack := SelectErase.Stack
abbrev Alphabet := SelectErase.Alphabet
abbrev Store := SelectErase.Store
inductive Label where
  | clear
  | body : SelectErase.Label → Label
  deriving DecidableEq
instance : Fintype Label where
  elems := insert .clear (Finset.univ.image Label.body)
  complete := by intro point;cases point <;> simp
instance : Inhabited Label := ⟨.clear⟩
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}

def program (found empty : Statement C) : Label → Statement C
  | .clear => .pop 4 B23_4_RatWordPrep.WholeCopy.capture (.branch (fun memory => memory.2.1)
      (.goto (fun _ => .clear)) (.goto (fun _ => .body (.candidate (.inr .clear)))))
  | .body .found => found
  | .body .empty => empty
  | .body point => LabelMap.statement Label.body (SelectErase.source point)
def source : Label → Statement C := program .halt .halt
def foundPort : Label := .body .found
def emptyPort : Label := .body .empty
theorem body_closed (point : SelectErase.Label) : source (C:=C) (.body point)=
    LabelMap.statement Label.body (SelectErase.source point) := by cases point <;> rfl
theorem body_agrees (found empty : Statement C) (point : SelectErase.Label)
    (nf : point≠.found) (ne : point≠.empty) :
    program found empty (.body point)=LabelMap.statement Label.body (SelectErase.source point) := by
  cases point <;> first | rfl | exact False.elim (nf rfl) | exact False.elim (ne rfl)

abbrev bank := SelectErase.bank
abbrev Work := SelectErase.Work
def state (bg : Stack → List Bool) (point : Label) (memory : Store C)
    (bits remaining tool cursor parked archive room temporary : List Bool) : State C :=
  ⟨some point,memory,bank bg bits remaining tool cursor parked archive room temporary⟩
def initial (bg : Stack → List Bool) (memory : Store C) (bits parent old4 old5 : List Bool) (k : Nat) : State C :=
  state bg .clear memory bits old4 old5 (ControllerCandidate.unary k) [] parent.reverse
    (ControllerCandidate.unary parent.length) []
theorem body_state (bg : Stack → List Bool) (point : SelectErase.Label) (memory : Store C)
    (bits remaining tool cursor parked archive room temporary : List Bool) :
    LabelMap.configuration Label.body (SelectErase.state bg point memory bits remaining tool cursor parked archive room temporary)=
      state bg (.body point) memory bits remaining tool cursor parked archive room temporary := rfl
theorem update_remaining (bg : Stack → List Bool) (bits remaining tool cursor parked archive room temporary next : List Bool) :
    Function.update (bank bg bits remaining tool cursor parked archive room temporary) 4 next=
      bank bg bits next tool cursor parked archive room temporary := by
  funext point;fin_cases point <;> rfl
theorem clear_bit (bg : Stack → List Bool) (memory : Store C) (bit : Bool)
    (bits remaining tool cursor parked archive room temporary : List Bool) :
    TM2.step source (state bg .clear memory bits (bit::remaining) tool cursor parked archive room temporary)=
      some (state bg .clear (memory.1,true,bit) bits remaining tool cursor parked archive room temporary) := by
  simp [source,program,state,TM2.step,TM2.stepAux,B23_4_RatWordPrep.WholeCopy.capture,
    bank,SelectErase.bank,update_remaining]
theorem clear_end (bg : Stack → List Bool) (memory : Store C)
    (bits tool cursor parked archive room temporary : List Bool) :
    TM2.step source (state bg .clear memory bits [] tool cursor parked archive room temporary)=
      some (state bg (.body (.candidate (.inr .clear))) (memory.1,false,false)
        bits [] tool cursor parked archive room temporary) := by
  simp [source,program,state,TM2.step,TM2.stepAux,B23_4_RatWordPrep.WholeCopy.capture,
    bank,SelectErase.bank,update_remaining]

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
end RootB236.Controller.ResumeErase
