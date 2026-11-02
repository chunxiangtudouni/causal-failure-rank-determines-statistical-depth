module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeInit_040

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.NatField

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PSTRSymbolicNaturalExport

abbrev Label := PSTRSymbolicNaturalExport.Label
abbrev Store (C : Type*) := PSTRSymbolicNaturalExport.Memory C
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := PSTRSymbolicNaturalExport.State C

variable {C : Type*}

/-- A single actual archived raw natural field. This reuses the established
fieldBody and restore program; no paired-record/lane ABI is assumed. -/
def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then
    .push 7 (fun _ => true)
      (.push 15 (fun _ => false) (.push 15 (fun _ => false)
        (.pop 1 captureBit (.push 7 savedBit (.push 7 (fun _ => false) (.goto (fun _ => 1)))))))
  else if point=1 then
    PSTRSymbolicRatExport.fieldBody 1 (.goto (fun _ => 3))
  else if point=3 then
    LabelMap.statement PSTRSymbolicRatExport.restoreLabel (PSTRSymbolicNaturalExport.program 2)
  else caller

theorem prepare_step (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    TM2.step (program .halt) (state (some 0) (context,(bit,flag,mode)) (false::left) scratch target background)=
      some (state (some 1) (context,(false,flag,mode)) left
        (false::false::true::scratch) (false::false::target) background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,savedBit,
    slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem data_step (context : C) (bit flag mode digit : Bool)
    (left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    TM2.step (program .halt) (state (some 1) (context,(bit,flag,mode)) (true::digit::left) scratch target background)=
      some (state (some 1) (context,(digit,true,mode)) left
        (false::digit::false::true::scratch) (true::digit::target) background) := by
  simp [program,PSTRSymbolicRatExport.fieldBody,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem end_step (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : RatInput.Stack → List Bool) :
    TM2.step (program .halt) (state (some 1) (context,(bit,flag,mode)) (false::left) scratch target background)=
      some (state (some 3) (context,(bit,false,mode)) left
        (false::false::scratch) target background) := by
  simp [program,PSTRSymbolicRatExport.fieldBody,state,TM2.step,TM2.stepAux,captureFlag,savedFlag,
    slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem restore_body {C : Type*} :
    program (C := C) .halt 3=PSTRSymbolicRatExport.ratProgram 3 := rfl

theorem final_body {C : Type*} : program (C := C) .halt 4=.halt := rfl

end B23_4_RatWordPrep.NatField
