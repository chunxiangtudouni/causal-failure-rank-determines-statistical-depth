module

public import B23_4_RatWordPrep_SeqCmp_HeaderNatRun_054
public import B23_4_RatWordPrep_SeqCmp_WholeCopyPublic_045

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.Rewind

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool

abbrev Store (C : Type*) := WholeCopy.Store C

inductive Label where
  | clear : Bool → Label
  | move | done
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.clear false⟩

abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def clearSlot (second : Bool) : RatInput.Stack := if second then 1 else 0

/-- Paid physical rewind after header lookahead: clear real0/1 cells,
reverse backup2 onto0, and return. A FALSE data bit is never an EOF test. -/
def program (caller : Statement C) : Label → Statement C
  | .clear second => .pop (clearSlot second) WholeCopy.capture
    (.branch WholeCopy.present (.goto (fun _ => .clear second))
      (.goto (fun _ => if second then .move else .clear true)))
  | .move => .pop 2 WholeCopy.capture (.branch WholeCopy.present
      (.push 0 WholeCopy.bit (.goto (fun _ => .move))) (.goto (fun _ => .done)))
  | .done => caller

def bank (background : RatInput.Stack → List Bool) (source archive backup : List Bool) : RatInput.Stack → List Bool :=
  fun slot => if slot=0 then source else if slot=1 then archive else if slot=2 then backup else background slot

def state (background : RatInput.Stack → List Bool) (point : Label) (memory : Store C)
    (source archive backup : List Bool) : State C := ⟨some point,memory,bank background source archive backup⟩

theorem clear0_bit (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (value : Bool) (source archive backup : List Bool) :
    TM2.step (program caller) (state background (.clear false) memory (value::source) archive backup)=
      some (state background (.clear false) (memory.1,true,value) source archive backup) := by
  simp [program,clearSlot,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present]
  funext slot
  fin_cases slot <;> rfl

theorem clear0_end (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (archive backup : List Bool) :
    TM2.step (program caller) (state background (.clear false) memory [] archive backup)=
      some (state background (.clear true) (memory.1,false,false) [] archive backup) := by
  simp [program,clearSlot,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present]

theorem clear1_bit (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (value : Bool) (source archive backup : List Bool) :
    TM2.step (program caller) (state background (.clear true) memory source (value::archive) backup)=
      some (state background (.clear true) (memory.1,true,value) source archive backup) := by
  simp [program,clearSlot,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present]
  funext slot
  fin_cases slot <;> rfl

theorem clear1_end (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source backup : List Bool) :
    TM2.step (program caller) (state background (.clear true) memory source [] backup)=
      some (state background .move (memory.1,false,false) source [] backup) := by
  simp [program,clearSlot,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present]

theorem move_bit (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (value : Bool) (source archive backup : List Bool) :
    TM2.step (program caller) (state background .move memory source archive (value::backup))=
      some (state background .move (memory.1,true,value) (value::source) archive backup) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present,WholeCopy.bit]
  funext slot
  fin_cases slot <;> rfl

theorem move_end (caller : Statement C) (background : RatInput.Stack → List Bool) (memory : Store C)
    (source archive : List Bool) :
    TM2.step (program caller) (state background .move memory source archive [])=
      some (state background .done (memory.1,false,false) source archive []) := by
  simp [program,state,bank,TM2.step,TM2.stepAux,WholeCopy.capture,WholeCopy.present]

end B23_4_RatWordPrep.Rewind
