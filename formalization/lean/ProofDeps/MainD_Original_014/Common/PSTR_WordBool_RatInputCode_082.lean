module

public import Common.PSTR_WordBool_RatOutputResources_081

/-! Actual source packet collector for the next original word consumer.
Only TRUE/data and both owned00 guards are consumed. Every source cell is
backed above the existing087 real sentinel and restored to15 by its SAME
restore code with fixed1/15 roles. Buffers3/4 hold reversed raw payloads;
the existing046 formatter will serialize their real reversed-back bits. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatInput

open Turing PSTRWordVM
open RationalControllerComputation
open PSTRSymbolicNaturalExport

abbrev Stack := Fin 16
abbrev Label := PSTRSymbolicNaturalExport.Label
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := PSTRSymbolicNaturalExport.Store
abbrev Memory (C : Type*) := C × Store
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Memory C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Memory C)

variable {C : Type*}

def restoreRoles : Stack ≃ Stack := Equiv.swap 1 15

def restoreBody : Statement C :=
  LabelMap.statement PSTRSymbolicRatExport.restoreLabel
    (StackIso.statement restoreRoles (PSTRSymbolicNaturalExport.program (C := C) 2))

def fieldBody (buffer : Stack) (again after : Label) : Statement C :=
  .pop 15 captureFlag (.push 7 savedFlag (.push 7 (fun _ => false)
    (.branch savedFlag
      (.pop 15 captureBit (.push 7 savedBit (.push 7 (fun _ => false)
        (.push buffer savedBit (.goto (fun _ => again))))))
      (.pop 15 captureBit (.push 7 savedBit (.push 7 (fun _ => false) (.goto (fun _ => after))))))))

def program (caller : Statement C) (point : Label) : Statement C :=
  if point = 0 then
    .push 7 (fun _ => true) (.push 13 (fun _ => true)
      (.pop 15 captureBit (.push 7 savedBit (.push 7 (fun _ => false)
        (.pop 15 captureMode (.push 7 positive (.push 7 (fun _ => false) (.goto (fun _ => 1)))))))))
  else if point = 1 then fieldBody 3 1 2
  else if point = 2 then fieldBody 4 2 3
  else if point = 3 then restoreBody else caller

def cells (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) : Stack → List Bool :=
  fun point => if point = 15 then source else if point = 7 then scratch else
    if point = 3 then numerator else if point = 4 then denominator else if point = 13 then raw else background point

def state (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (source scratch numerator denominator raw : List Bool) : State C :=
  ⟨some point,(context,memory),cells background source scratch numerator denominator raw⟩

theorem source_at (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) :
    cells background source scratch numerator denominator raw 15 = source := rfl
theorem scratch_at (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) :
    cells background source scratch numerator denominator raw 7 = scratch := rfl
theorem numerator_at (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) :
    cells background source scratch numerator denominator raw 3 = numerator := rfl
theorem denominator_at (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) :
    cells background source scratch numerator denominator raw 4 = denominator := rfl
theorem raw_at (background : Stack → List Bool) (source scratch numerator denominator raw : List Bool) :
    cells background source scratch numerator denominator raw 13 = raw := rfl

theorem update_source (background : Stack → List Bool) (source scratch numerator denominator raw next : List Bool) :
    Function.update (cells background source scratch numerator denominator raw) 15 next =
      cells background next scratch numerator denominator raw := by funext point; fin_cases point <;> rfl
theorem update_scratch (background : Stack → List Bool) (source scratch numerator denominator raw next : List Bool) :
    Function.update (cells background source scratch numerator denominator raw) 7 next =
      cells background source next numerator denominator raw := by funext point; fin_cases point <;> rfl
theorem update_numerator (background : Stack → List Bool) (source scratch numerator denominator raw next : List Bool) :
    Function.update (cells background source scratch numerator denominator raw) 3 next =
      cells background source scratch next denominator raw := by funext point; fin_cases point <;> rfl
theorem update_denominator (background : Stack → List Bool) (source scratch numerator denominator raw next : List Bool) :
    Function.update (cells background source scratch numerator denominator raw) 4 next =
      cells background source scratch numerator next raw := by funext point; fin_cases point <;> rfl
theorem update_raw (background : Stack → List Bool) (source scratch numerator denominator raw next : List Bool) :
    Function.update (cells background source scratch numerator denominator raw) 13 next =
      cells background source scratch numerator denominator next := by funext point; fin_cases point <;> rfl

theorem start_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (source scratch numerator denominator raw : List Bool) :
    TM2.step (program caller) (state background 0 context memory (true::negative::source) scratch numerator denominator raw) =
      some (state background 1 context (true,memory.2.1,negative) source
        (false::negative::false::true::true::scratch) numerator denominator (true::raw)) := by
  simp [state,program,TM2.step,TM2.stepAux,captureBit,captureMode,savedBit,positive,
    source_at,scratch_at,raw_at,update_source,update_scratch,update_raw]

theorem numerator_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag mode digit : Bool) (source scratch numerator denominator raw : List Bool) :
    TM2.step (program caller) (state background 1 context (bit,flag,mode)
      (true::digit::source) scratch numerator denominator raw) =
      some (state background 1 context (digit,true,mode) source
        (false::digit::false::true::scratch) (digit::numerator) denominator raw) := by
  simp [state,program,fieldBody,TM2.step,TM2.stepAux,captureFlag,captureBit,savedFlag,savedBit,
    source_at,scratch_at,numerator_at,update_source,update_scratch,update_numerator]

theorem denominator_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag mode digit : Bool) (source scratch numerator denominator raw : List Bool) :
    TM2.step (program caller) (state background 2 context (bit,flag,mode)
      (true::digit::source) scratch numerator denominator raw) =
      some (state background 2 context (digit,true,mode) source
        (false::digit::false::true::scratch) numerator (digit::denominator) raw) := by
  simp [state,program,fieldBody,TM2.step,TM2.stepAux,captureFlag,captureBit,savedFlag,savedBit,
    source_at,scratch_at,denominator_at,update_source,update_scratch,update_denominator]

theorem numerator_end (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag mode : Bool) (source scratch numerator denominator raw : List Bool) :
    TM2.step (program caller) (state background 1 context (bit,flag,mode)
      (false::false::source) scratch numerator denominator raw) =
      some (state background 2 context (false,false,mode) source
        (false::false::false::false::scratch) numerator denominator raw) := by
  simp [state,program,fieldBody,TM2.step,TM2.stepAux,captureFlag,captureBit,savedFlag,savedBit,
    source_at,scratch_at,update_source,update_scratch]

theorem denominator_end (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag mode : Bool) (source scratch numerator denominator raw : List Bool) :
    TM2.step (program caller) (state background 2 context (bit,flag,mode)
      (false::false::source) scratch numerator denominator raw) =
      some (state background 3 context (false,false,mode) source
        (false::false::false::false::scratch) numerator denominator raw) := by
  simp [state,program,fieldBody,TM2.step,TM2.stepAux,captureFlag,captureBit,savedFlag,savedBit,
    source_at,scratch_at,update_source,update_scratch]

end PaperProofs.Common.Native.PSTRWordBool.RatInput
