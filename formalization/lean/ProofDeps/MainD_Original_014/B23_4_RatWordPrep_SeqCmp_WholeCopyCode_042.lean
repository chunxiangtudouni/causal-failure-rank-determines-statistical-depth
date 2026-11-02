module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeInit_040

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.WholeCopy

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

inductive Label where
  | boot | copy | restore | done
  deriving DecidableEq
instance : Fintype Label :=
  ⟨{.boot,.copy,.restore,.done},by intro point; cases point <;> simp⟩
instance : Inhabited Label := ⟨.boot⟩

abbrev Store (C : Type*) := C × Bool × Bool
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def capture (memory : Store C) (cell : Option Bool) : Store C := (memory.1,cell.isSome,cell.getD false)
def present (memory : Store C) : Bool := memory.2.1
def bit (memory : Store C) : Bool := memory.2.2

/-- Copy every real source0 cell, including FALSE cells. The fresh TRUE
on3 delimits only owned backups; source0 is restored and2 gets its reverse. -/
def program (caller : Statement C) : Label → Statement C
  | .boot => .push 3 (fun _ => true) (.goto (fun _ => .copy))
  | .copy => .pop 0 capture (.branch present
    (.push 2 bit (.push 3 bit (.push 3 (fun _ => false) (.goto (fun _ => .copy)))))
    (.goto (fun _ => .restore)))
  | .restore => .pop 3 capture (.branch bit (.goto (fun _ => .done))
    (.pop 3 capture (.push 0 bit (.goto (fun _ => .restore)))))
  | .done => caller

def bank (background : RatInput.Stack → List Bool) (source backup scratch : List Bool) : RatInput.Stack → List Bool :=
  fun slot => if slot=0 then source else if slot=2 then backup else if slot=3 then scratch else background slot
def state (background : RatInput.Stack → List Bool) (point : Label) (memory : Store C)
    (source backup scratch : List Bool) : State C := ⟨some point,memory,bank background source backup scratch⟩

theorem boot_step (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source backup scratch : List Bool) :
    TM2.step (program caller) (state background .boot memory source backup scratch)=
      some (state background .copy memory source backup (true::scratch)) := by
  simp [program,state,bank,TM2.step,TM2.stepAux]
  funext slot
  fin_cases slot <;> rfl

theorem copy_bit (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (value : Bool) (source backup scratch : List Bool) :
    TM2.step (program caller) (state background .copy memory (value::source) backup scratch)=
      some (state background .copy (memory.1,true,value) source (value::backup) (false::value::scratch)) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,capture,present,bit]
  funext slot
  fin_cases slot <;> rfl

theorem copy_end (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (backup scratch : List Bool) :
    TM2.step (program caller) (state background .copy memory [] backup scratch)=
      some (state background .restore (memory.1,false,false) [] backup scratch) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,capture,present,bit]

theorem restore_bit (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (value : Bool) (source backup scratch : List Bool) :
    TM2.step (program caller) (state background .restore memory source backup (false::value::scratch))=
      some (state background .restore (memory.1,true,value) (value::source) backup scratch) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,capture,bit]
  funext slot
  fin_cases slot <;> rfl

theorem restore_end (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source backup scratch : List Bool) :
    TM2.step (program caller) (state background .restore memory source backup (true::scratch))=
      some (state background .done (memory.1,true,true) source backup scratch) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,capture,bit]
  funext slot
  fin_cases slot <;> rfl

end B23_4_RatWordPrep.WholeCopy
