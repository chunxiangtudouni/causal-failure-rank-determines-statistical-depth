module

public import Common.PSTR_WordBool_RatInputAPI_093

/-! The actual two-packet collector. Both signs live only in Boolean
memory. The four fields use the frozen paid field-copy loops; one sentinel
backs every consumed cell and the unchanged087 restore restores all15. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector

open Turing PSTRWordVM RationalControllerComputation

abbrev Stack := RatInput.Stack
abbrev Label := Fin 8
abbrev Store (C : Type*) := RatInput.Encoder.Store (C × Bool × Bool)
abbrev Statement (C : Type*) := TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def bank (background : Stack → List Bool) (source scratch xn xd yn yd : List Bool) : Stack → List Bool :=
  fun slot => if slot=15 then source else if slot=7 then scratch else if slot=8 then xn else
    if slot=9 then xd else if slot=3 then yn else if slot=4 then yd else background slot

def state (background : Stack → List Bool) (point : Label) (context : C) (sx sy : Bool)
    (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch xn xd yn yd : List Bool) : State C :=
  ⟨some point,(((context,sx,sy),memory),formatter),bank background source scratch xn xd yn yd⟩

def captureBit (memory : Store C) (value : Option Bool) : Store C :=
  ((memory.1.1,(value.getD false,memory.1.2.2)),memory.2)
def captureMode (memory : Store C) (value : Option Bool) : Store C :=
  ((memory.1.1,(memory.1.2.1,memory.1.2.2.1,value.getD false)),memory.2)
def savedBit (memory : Store C) : Bool := memory.1.2.1
def savedMode (memory : Store C) : Bool := memory.1.2.2.2

def saveSign (later : Bool) (memory : Store C) : Store C :=
  (((memory.1.1.1,
      if later then memory.1.1.2.1 else savedMode memory,
      if later then savedMode memory else memory.1.1.2.2),memory.1.2),memory.2)

def headerBody (later : Bool) : Statement C :=
  .pop 15 captureBit (.push 7 savedBit (.push 7 (fun _=>false)
    (.pop 15 captureMode (.push 7 savedMode (.push 7 (fun _=>false)
      (.load (saveSign later) (.goto (fun _=>if later then 4 else 1))))))))

def fieldRoles (later : Bool) : Stack ≃ Stack :=
  if later then Equiv.refl _ else (Equiv.swap 3 8).trans (Equiv.swap 4 9)

def fieldLabel (later : Bool) (point : RatInput.Label) : Label :=
  if point=1 then (if later then 4 else 1) else if point=2 then (if later then 5 else 2)
  else (if later then 6 else 3)

def restoreLabel (point : RatInput.Label) : Label := if point=3 then 6 else 7

def fieldBody (later second : Bool) : Statement C :=
  LabelMap.statement (fieldLabel later)
    (StoreIso.statement (RatInput.Encoder.exchange (C × Bool × Bool))
      (StackIso.statement (fieldRoles later)
        (RatInput.program (C:=(C × Bool × Bool) × WordNatIO.Store) .halt (if second then 2 else 1))))

def restoreBody : Statement C :=
  LabelMap.statement restoreLabel
    (StoreIso.statement (RatInput.Encoder.exchange (C × Bool × Bool))
      (RatInput.restoreBody (C:=(C × Bool × Bool) × WordNatIO.Store)))

def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then .push 7 (fun _=>true) (headerBody false)
  else if point=1 then fieldBody false false
  else if point=2 then fieldBody false true
  else if point=3 then headerBody true
  else if point=4 then fieldBody true false
  else if point=5 then fieldBody true true
  else if point=6 then restoreBody else caller

def fieldConfiguration (later : Bool)
    (before : RatInput.State ((C × Bool × Bool) × WordNatIO.Store)) : State C :=
  LabelMap.configuration (fieldLabel later)
    (StoreIso.configuration (RatInput.Encoder.exchange (C × Bool × Bool))
      (StackIso.configuration (fieldRoles later) before))

def restoreConfiguration (before : RatInput.State ((C × Bool × Bool) × WordNatIO.Store)) : State C :=
  LabelMap.configuration restoreLabel
    (StoreIso.configuration (RatInput.Encoder.exchange (C × Bool × Bool)) before)

theorem source_at (background : Stack → List Bool) (source scratch xn xd yn yd : List Bool) :
    bank background source scratch xn xd yn yd 15=source := rfl
theorem scratch_at (background : Stack → List Bool) (source scratch xn xd yn yd : List Bool) :
    bank background source scratch xn xd yn yd 7=scratch := rfl

theorem update_source (background : Stack → List Bool) (source scratch xn xd yn yd next : List Bool) :
    Function.update (bank background source scratch xn xd yn yd) 15 next =
      bank background next scratch xn xd yn yd := by funext slot;fin_cases slot <;> rfl

theorem update_scratch (background : Stack → List Bool) (source scratch xn xd yn yd next : List Bool) :
    Function.update (bank background source scratch xn xd yn yd) 7 next =
      bank background source next xn xd yn yd := by funext slot;fin_cases slot <;> rfl

theorem start_x_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (sx sy negative : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch xn xd yn yd : List Bool) :
    TM2.step (program caller) (state background 0 context sx sy memory formatter
      (true::negative::source) scratch xn xd yn yd) =
      some (state background 1 context negative sy (true,memory.2.1,negative) formatter source
        (false::negative::false::true::true::scratch) xn xd yn yd) := by
  simp [program,state,headerBody,TM2.step,TM2.stepAux,captureBit,captureMode,savedBit,savedMode,
    saveSign,source_at,scratch_at,update_source,update_scratch]

theorem start_y_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (sx sy negative : Bool) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (source scratch xn xd yn yd : List Bool) :
    TM2.step (program caller) (state background 3 context sx sy memory formatter
      (true::negative::source) scratch xn xd yn yd) =
      some (state background 4 context sx negative (true,memory.2.1,negative) formatter source
        (false::negative::false::true::scratch) xn xd yn yd) := by
  simp [program,state,headerBody,TM2.step,TM2.stepAux,captureBit,captureMode,savedBit,savedMode,
    saveSign,source_at,scratch_at,update_source,update_scratch]

end PaperProofs.Common.Native.PSTRWordBool.RatPair.Collector
