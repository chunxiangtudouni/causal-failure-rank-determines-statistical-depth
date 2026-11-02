module
public import B23_4_RatWordPrep_SeqCmp_WholeCopyPublic_045

/-! Static reuse of the actual EOF-driven WholeCopy reverse backup.
These wrappers contain no mask-dependent code or free physical reversal. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.MaskArchive
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
abbrev Whole := B23_4_RatWordPrep.WholeCopy.Label
abbrev Stack := RatInput.Stack
abbrev Label := B23_4_RatWordPrep.WholeCopy.Label
abbrev Store := B23_4_RatWordPrep.WholeCopy.Store
abbrev Statement := B23_4_RatWordPrep.WholeCopy.Statement
abbrev State := B23_4_RatWordPrep.WholeCopy.State
variable {C : Type*}

def program (roles : Stack ≃ Stack) (caller : Statement C) (point : Label) : Statement C :=
  if point=.done then caller else StackIso.statement roles (B23_4_RatWordPrep.WholeCopy.program .halt point)

theorem program_done (roles : Stack ≃ Stack) (caller : Statement C) : program roles caller .done=caller := rfl
theorem program_internal (roles : Stack ≃ Stack) (caller : Statement C) (point : Label) (proper : point≠.done) :
    program roles caller point=StackIso.statement roles (B23_4_RatWordPrep.WholeCopy.program .halt point) := by
  simp only [program,proper,ite_false]
theorem program_closed (roles : Stack ≃ Stack) (point : Label) :
    program (C:=C) roles .halt point=StackIso.statement roles (B23_4_RatWordPrep.WholeCopy.program .halt point) := by
  cases point <;> rfl

def bank (roles : Stack ≃ Stack) (background : Stack → List Bool) (input backup scratch : List Bool) : Stack → List Bool :=
  fun slot => if slot=roles 0 then input else if slot=roles 2 then backup else if slot=roles 3 then scratch else background slot
def state (roles : Stack ≃ Stack) (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input backup scratch : List Bool) : State C := ⟨some point,memory,bank roles background input backup scratch⟩
def Work (roles : Stack ≃ Stack) (slot : Stack) : Prop := slot=roles 0 ∨ slot=roles 2 ∨ slot=roles 3

theorem work_iff (roles : Stack ≃ Stack) (slot : Stack) :
    Work roles slot ↔ B23_4_RatWordPrep.WholeCopy.Work (roles.symm slot) := by
  simp only [Work,B23_4_RatWordPrep.WholeCopy.Work,Equiv.symm_apply_eq]

theorem bank_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (input backup scratch : List Bool) :
    bank roles background input backup scratch=
      StackIso.slots roles (B23_4_RatWordPrep.WholeCopy.bank (StackIso.slots roles.symm background) input backup scratch) := by
  funext slot
  simp only [bank,StackIso.slots,B23_4_RatWordPrep.WholeCopy.bank,Equiv.symm_apply_eq,Equiv.symm_symm,Equiv.apply_symm_apply]
theorem state_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input backup scratch : List Bool) :
    state roles background point memory input backup scratch=
      StackIso.configuration roles
        (B23_4_RatWordPrep.WholeCopy.state (StackIso.slots roles.symm background) point memory input backup scratch) := by
  rw [state,bank_eq];rfl
theorem occupied_slots (roles : Stack ≃ Stack) (before : Stack → List Bool) :
    RatInput.occupied (StackIso.slots roles before)=RatInput.occupied before := StackIso.occupied_sum roles before

def coefficient : Nat := B23_4_RatWordPrep.WholeCopy.coefficient
def inputScale (roles : Stack ≃ Stack) (background : Stack → List Bool) (input backup scratch : List Bool) : Nat :=
  RatInput.occupied (bank roles background input backup scratch)+1
theorem scale_eq (roles : Stack ≃ Stack) (background : Stack → List Bool) (input backup scratch : List Bool) :
    inputScale roles background input backup scratch=
      B23_4_RatWordPrep.WholeCopy.inputScale (StackIso.slots roles.symm background) input backup scratch := by
  rw [inputScale,bank_eq,occupied_slots];rfl

theorem clock_statement (roles : Stack ≃ Stack) (body : Statement C) (memory : Store C) (before : Stack → List Bool) :
    ScannerStatement.clock (StackIso.statement roles body) memory (StackIso.slots roles before)=
      ScannerStatement.clock body memory before := by
  induction body generalizing memory before with
  | push point value tail ih =>
    simp only [StackIso.statement,ScannerStatement.clock,StackIso.slots_at]
    rw [←StackIso.slots_update,ih]
  | pop point value tail ih =>
    simp only [StackIso.statement,ScannerStatement.clock,StackIso.slots_at]
    rw [←StackIso.slots_update,ih]
  | peek point value tail ih => simp only [StackIso.statement,ScannerStatement.clock,StackIso.slots_at,ih]
  | load value tail ih => exact ih (value memory) before
  | branch test yes no yesIH noIH =>
    cases choice : test memory <;>
      simp only [StackIso.statement,ScannerStatement.clock,choice,Bool.false_eq_true,ite_false,ite_true,yesIH,noIH]
  | goto _ | halt => rfl

def support : Finset Label := Finset.univ
private theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro _;exact Finset.mem_univ _
  | halt => trivial
theorem supports (roles : Stack ≃ Stack) (caller : Statement C) : TM2.Supports (program roles caller) support :=
  ⟨Finset.mem_univ _,fun _ _ => supports_stmt _⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance

end RootB236.Controller.MaskArchive
