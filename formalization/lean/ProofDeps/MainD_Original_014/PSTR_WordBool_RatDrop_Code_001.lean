module

public import Common.PSTR_WordBool_RatInputAPI_093

/-! One fixed physical packet consumer: park the result, really discard
two old operand packets, then reuse076 to return the result to15. The
packet grammar supplies the four guards; no numeric width enters control. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation

abbrev Stack:=RatInput.Stack
abbrev Label:=Fin 11
abbrev Store (C : Type*):=C×RatOutput.Store
abbrev Statement (C : Type*):=TM2.Stmt RatInput.Alphabet Label (Store C)
abbrev State (C : Type*):=TM2.Cfg RatInput.Alphabet Label (Store C)

variable {C : Type*}

def capture (memory : Store C) (cell : Option Bool) : Store C :=
  (memory.1,(cell.isSome,cell.getD false))

def bit (memory : Store C) : Bool:=memory.2.2

def put (keep : Bool) (next : Statement C) : Statement C :=if keep then .push 3 bit next else next

def headerBody (keep : Bool) (next : Label) : Statement C :=
  .pop 15 capture (put keep (.pop 15 capture (put keep (.goto (fun _=>next)))))

def fieldBody (keep : Bool) (again next : Label) : Statement C :=
  .pop 15 capture (put keep (.branch bit
    (.pop 15 capture (put keep (.goto (fun _=>again))))
    (.pop 15 capture (put keep (.goto (fun _=>next))))))

def reverseRoles : Stack≃Stack:=Equiv.swap 14 3
def reverseLabel (point : RatOutput.Label) : Label:=if point=7 then 9 else 10

def program (caller : Statement C) (point : Label) : Statement C :=
  match point.val with
  | 0=>headerBody true 1
  | 1=>fieldBody true 1 2
  | 2=>fieldBody true 2 3
  | 3=>headerBody false 4
  | 4=>fieldBody false 4 5
  | 5=>fieldBody false 5 6
  | 6=>headerBody false 7
  | 7=>fieldBody false 7 8
  | 8=>fieldBody false 8 9
  | 9=>LabelMap.statement reverseLabel (StackIso.statement reverseRoles (RatOutput.program .halt 7))
  | _=>caller

def cells (background : Stack→List Bool) (source parked : List Bool) : Stack→List Bool :=
  fun slot=>if slot=15 then source else if slot=3 then parked else background slot

def state (background : Stack→List Bool) (point : Label) (context : C) (memory : RatOutput.Store)
    (source parked : List Bool) : State C :=⟨some point,(context,memory),cells background source parked⟩

theorem source_at (background : Stack→List Bool) (source parked : List Bool) : cells background source parked 15=source:=rfl
theorem parked_at (background : Stack→List Bool) (source parked : List Bool) : cells background source parked 3=parked:=rfl

theorem update_source (background : Stack→List Bool) (source parked next : List Bool) :
    Function.update (cells background source parked) 15 next=cells background next parked := by
  funext slot;fin_cases slot <;> rfl

theorem update_parked (background : Stack→List Bool) (source parked next : List Bool) :
    Function.update (cells background source parked) 3 next=cells background source next := by
  funext slot;fin_cases slot <;> rfl

theorem header_step (caller : Statement C) (keep : Bool) (point next : Label)
    (code : program caller point=headerBody keep next) (background : Stack→List Bool)
    (context : C) (memory : RatOutput.Store) (negative : Bool) (source parked : List Bool) :
    TM2.step (program caller) (state background point context memory (true::negative::source) parked)=
      some (state background next context (true,negative) source (if keep then negative::true::parked else parked)) := by
  change some (TM2.stepAux (program caller point) _ _)=_
  rw [code]
  cases keep <;> simp [headerBody,put,TM2.stepAux,capture,bit,state,source_at,parked_at,update_source,update_parked]

theorem field_bit (caller : Statement C) (keep : Bool) (point next : Label)
    (code : program caller point=fieldBody keep point next) (background : Stack→List Bool)
    (context : C) (memory : RatOutput.Store) (digit : Bool) (source parked : List Bool) :
    TM2.step (program caller) (state background point context memory (true::digit::source) parked)=
      some (state background point context (true,digit) source (if keep then digit::true::parked else parked)) := by
  change some (TM2.stepAux (program caller point) _ _)=_
  rw [code]
  cases keep <;> simp [fieldBody,put,TM2.stepAux,capture,bit,state,source_at,parked_at,update_source,update_parked]

theorem field_end (caller : Statement C) (keep : Bool) (point next : Label)
    (code : program caller point=fieldBody keep point next) (background : Stack→List Bool)
    (context : C) (memory : RatOutput.Store) (source parked : List Bool) :
    TM2.step (program caller) (state background point context memory (false::false::source) parked)=
      some (state background next context (true,false) source (if keep then false::false::parked else parked)) := by
  change some (TM2.stepAux (program caller point) _ _)=_
  rw [code]
  cases keep <;> simp [fieldBody,put,TM2.stepAux,capture,bit,state,source_at,parked_at,update_source,update_parked]

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
