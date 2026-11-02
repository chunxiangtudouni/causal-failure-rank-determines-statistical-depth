module

public import Common.PSTR_SYM_NaturalExportFinite_090
public import Common.PSTR_WordVM_LabelMap_029

/-! Concrete215 word-prior archive exporter, not Rat arithmetic. The two
actual LEFT fields have TRUE/data pairs and single FALSE guards. It copies
DEN then NUM into owned self-delimiting destination15, copies actual sign,
and restores source1/old7 with frozen087's physically pushed sentinel. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport

open Turing PaperProofs.Common.Native.PSTRWordVM PSTRSymbolicNaturalExport

def restoreLabel (label : Label) : Label := if label = 2 then 3 else 4

def fieldBody {C : Type*} (again : Label) (after : TM2.Stmt Alphabet Label (Memory C)) :
    TM2.Stmt Alphabet Label (Memory C) :=
  .pop 1 captureFlag
    (.branch savedFlag
      (.push 7 savedFlag (.push 7 (fun _ => false)
        (.pop 1 captureBit (.push 7 savedBit (.push 7 (fun _ => false)
          (.push 15 savedBit (.push 15 (fun _ => true) (.goto (fun _ => again)))))))))
      (.push 7 savedFlag (.push 7 (fun _ => false) after)))

def ratProgram {C : Type*} (label : Label) : TM2.Stmt Alphabet Label (Memory C) :=
  if label = 0 then
    .push 7 (fun _ => true)
      (.push 15 (fun _ => false) (.push 15 (fun _ => false)
        (.pop 1 captureBit (.push 7 savedBit (.push 7 (fun _ => false) (.goto (fun _ => 1)))))))
  else if label = 1 then
    fieldBody 1 (.push 15 (fun _ => false) (.push 15 (fun _ => false) (.goto (fun _ => 2))))
  else if label = 2 then
    fieldBody 2 (.pop 1 captureBit (.push 7 savedBit (.push 7 (fun _ => false)
      (.push 15 savedBit (.push 15 (fun _ => true) (.goto (fun _ => 3)))))))
  else if label = 3 then
    LabelMap.statement restoreLabel (program 2)
  else .halt

theorem prepare_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step ratProgram (state (some 0) (context,(bit,flag,mode)) (false :: left) scratch target background) =
      some (state (some 1) (context,(false,flag,mode)) left
        (false :: false :: true :: scratch) (false :: false :: target) background) := by
  simp [ratProgram,state,TM2.step,TM2.stepAux,captureBit,savedBit,
    slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem data_step {C : Type*} (context : C) (bit flag mode digit secondField : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step ratProgram (state (some (if secondField then 2 else 1)) (context,(bit,flag,mode))
      (true :: digit :: left) scratch target background) =
      some (state (some (if secondField then 2 else 1)) (context,(digit,true,mode)) left
        (false :: digit :: false :: true :: scratch) (true :: digit :: target) background) := by
  cases secondField <;>
    simp [ratProgram,fieldBody,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
      slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem denominator_end_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step ratProgram (state (some 1) (context,(bit,flag,mode)) (false :: left) scratch target background) =
      some (state (some 2) (context,(bit,false,mode)) left
        (false :: false :: scratch) (false :: false :: target) background) := by
  simp [ratProgram,fieldBody,state,TM2.step,TM2.stepAux,captureFlag,savedFlag,
    slots_left,slots_scratch,slots_target,update_scratch,update_left,update_target]

theorem numerator_end_step {C : Type*} (context : C) (bit flag mode negative : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step ratProgram (state (some 2) (context,(bit,flag,mode)) (false :: negative :: left) scratch target background) =
      some (state (some 3) (context,(negative,false,mode)) left
        (false :: negative :: false :: false :: scratch) (true :: negative :: target) background) := by
  simp [ratProgram,fieldBody,state,TM2.step,TM2.stepAux,captureFlag,captureBit,savedFlag,savedBit,
    slots_left,slots_scratch,slots_target,update_scratch,update_left,update_target]

theorem restore_body {C : Type*} :
    ratProgram (C := C) 3 = LabelMap.statement restoreLabel (program 2) := rfl

theorem restore_label_two : restoreLabel 2 = 3 := rfl

theorem restore_label_port (mode : Bool) : restoreLabel (if mode then 4 else 3) = 4 := by
  cases mode <;> rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRatExport
